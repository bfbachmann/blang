use colored::Colorize;

use crate::analyzer::ast::func::{analyze_fn_sig, AFnSig};
use crate::analyzer::ast::program::AProgram;
use crate::analyzer::ast::spec::ASpec;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::move_check::MoveChecker;
use crate::analyzer::prog_context::{ProgramAnalysis, ProgramContext};
use crate::analyzer::type_containment::{check_enum_containment, check_struct_containment};
use crate::analyzer::warn::{AnalyzeWarning, WarnKind};
use crate::parser::ext::Extern;
use crate::parser::func::Function;
use crate::parser::program::Program;
use crate::parser::r#impl::Impl;
use crate::parser::spec::Spec;
use crate::parser::statement::Statement;

/// Performs semantic analysis on the given program and extern functions.
pub fn analyze_prog(prog: &Program) -> ProgramAnalysis {
    let mut ctx = ProgramContext::new();

    define_types(&mut ctx, prog);
    define_fns(&mut ctx, prog);

    // Perform semantic analysis on the program.
    let prog = AProgram::from(&mut ctx, prog);

    // Perform move checks and add any errors to our list of errors only if semantic analysis
    // passed.
    if ctx.errors().is_empty() {
        let errors = MoveChecker::check_prog(&prog, ctx.type_store());
        for err in errors {
            ctx.insert_err(err);
        }
    }

    ProgramAnalysis::from(ctx, prog)
}

/// Defines top-level types and specs in the program context without deeply analyzing their fields,
/// so they can be referenced later. This will simply check for type name collisions and
/// containment cycles. We do this before fully analyzing types to prevent infinite recursion.
fn define_types(ctx: &mut ProgramContext, prog: &Program) {
    // First pass: Define all types without analyzing their fields. In this pass, we will only
    // check that there are no type name collisions.
    for statement in &prog.statements {
        match statement {
            Statement::StructDeclaration(struct_type) => {
                ctx.try_insert_unchecked_struct_type(struct_type.clone());
            }

            Statement::EnumDeclaration(enum_type) => {
                ctx.try_insert_unchecked_enum_type(enum_type.clone());
            }

            Statement::SpecDeclaration(spec) => ctx.try_insert_unchecked_spec(spec.clone()),

            _ => {}
        }
    }

    // Second pass: Check for type containment cycles.
    let mut results = vec![];
    {
        let extern_structs = ctx.unchecked_struct_types();
        for struct_type in extern_structs {
            let result = check_struct_containment(ctx, struct_type, &mut vec![]);
            results.push((result, struct_type.name.clone()));
        }

        let extern_enums = ctx.unchecked_enum_types();
        for enum_type in extern_enums {
            let result = check_enum_containment(ctx, enum_type, &mut vec![]);
            results.push((result, enum_type.name.clone()));
        }
    }

    // Remove types that have illegal containment cycles from the program context and add them as
    // invalid types instead. We do this so we can safely continue with semantic analysis without
    // having to worry about stack overflows during recursive type resolution.
    for (result, type_name) in results {
        if ctx.consume_error(result).is_none() {
            ctx.remove_unchecked_struct_type(type_name.as_str());
            ctx.remove_unchecked_enum_type(type_name.as_str());
            ctx.insert_invalid_type_name(type_name.as_str());
        }
    }
}

/// Analyzes all top-level function signatures (this includes those inside specs) and defines them
/// in the program context so they can be referenced later. This will not perform any analysis of
/// function bodies.
fn define_fns(ctx: &mut ProgramContext, prog: &Program) {
    let mut main_defined = false;

    for statement in &prog.statements {
        match statement {
            Statement::FunctionDeclaration(func) => {
                define_fn(ctx, func);

                if func.signature.name == "main" {
                    main_defined = true;
                }
            }

            Statement::ExternFns(ext) => {
                define_extern_fns(ctx, ext);
            }

            Statement::Impl(impl_) => {
                define_impl(ctx, impl_);
            }

            Statement::SpecDeclaration(spec) => {
                define_spec(ctx, spec);
            }

            _ => {}
        };
    }

    if !main_defined {
        ctx.insert_warn(AnalyzeWarning::new_with_default_pos(
            WarnKind::MissingMain,
            "no main function was detected; your code will not execute",
        ));
    }
}

fn define_fn(ctx: &mut ProgramContext, func: &Function) {
    analyze_fn_sig(ctx, &func.signature);

    if func.signature.name == "main" {
        // Make sure main has no args or return.
        if func.signature.args.len() != 0 {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::InvalidMain,
                format_code!("function {} cannot have arguments", "main").as_str(),
                &func.signature,
            ));
        }

        if func.signature.maybe_ret_type.is_some() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::InvalidMain,
                format_code!("function {} cannot have a return type", "main").as_str(),
                &func.signature,
            ));
        }
    }
}

fn define_extern_fns(ctx: &mut ProgramContext, ext: &Extern) {
    for sig in &ext.fn_sigs {
        if sig.tmpl_params.is_some() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::InvalidExtern,
                "external functions cannot be templated",
                sig,
            ));
            continue;
        }

        analyze_fn_sig(ctx, sig);
    }
}

fn define_impl(ctx: &mut ProgramContext, impl_: &Impl) {
    // Set the current impl type key on the program context so we can access it when
    // resolving type `This`.
    let impl_type_key = ctx.resolve_type(&impl_.typ);
    ctx.set_cur_this_type_key(Some(impl_type_key));

    // Analyze each member function signature and record it as a member of this type
    // in the program context.
    for member_fn in &impl_.member_fns {
        let fn_sig = AFnSig::from(ctx, &member_fn.signature);

        // Make sure this isn't a duplicate member function.
        if ctx
            .get_member_fn(impl_type_key, fn_sig.name.as_str())
            .is_some()
        {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::DuplicateFunction,
                format_code!(
                    "function {} was already defined for type {}",
                    member_fn.signature.name,
                    ctx.display_type_for_key(impl_type_key),
                )
                .as_str(),
                &member_fn.signature,
            ));
        } else {
            ctx.insert_member_fn(impl_type_key, fn_sig);
        }
    }

    ctx.set_cur_this_type_key(None);
}

fn define_spec(ctx: &mut ProgramContext, spec: &Spec) {
    // Make sure this spec name is not a duplicate.
    if ctx.get_spec(spec.name.as_str()).is_some() {
        // Record the error and return a placeholder value.
        ctx.insert_err(AnalyzeError::new(
            ErrorKind::DuplicateSpec,
            format_code!("another spec named {} already exists", spec.name).as_str(),
            spec,
        ));

        return;
    }

    // Analyze the spec and add it to the program context so we can retrieve and render
    // it later.
    let a_spec = ASpec::from(ctx, spec);
    ctx.insert_spec(a_spec);
}
