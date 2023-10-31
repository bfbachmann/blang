use std::collections::HashMap;

use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func_sig::analyze_fn_sig;
use crate::analyzer::func_sig::RichFnSig;
use crate::analyzer::move_check::MoveChecker;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#enum::check_enum_containment_cycles;
use crate::analyzer::r#struct::check_struct_containment_cycles;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::analyzer::spec::RichSpec;
use crate::analyzer::statement::RichStatement;
use crate::analyzer::warn::{AnalyzeWarning, WarnKind};
use crate::format_code;
use crate::parser::program::Program;
use crate::parser::statement::Statement;

/// Represents a semantically valid and type-rich program.
#[derive(Debug)]
pub struct RichProg {
    pub statements: Vec<RichStatement>,
}

/// Represents the result of semantic analysis on a program.
pub struct ProgramAnalysis {
    pub prog: RichProg,
    pub types: HashMap<TypeId, RichType>,
    pub errors: Vec<AnalyzeError>,
    pub warnings: Vec<AnalyzeWarning>,
}

impl RichProg {
    /// Performs semantic analysis on the given program and extern functions.
    pub fn analyze(prog: Program) -> ProgramAnalysis {
        let mut ctx = ProgramContext::new();

        // Perform semantic analysis on the program.
        let prog = RichProg::from(&mut ctx, prog);
        let mut errors = ctx.errors();
        let warnings = ctx.warnings();
        let types = ctx.types();

        // Perform move checks and add any errors to our list of errors only if semantic analysis
        // passed.
        if errors.is_empty() {
            errors = MoveChecker::check_prog(&prog, &types);
        }

        ProgramAnalysis {
            prog,
            warnings,
            errors,
            types,
        }
    }

    /// Performs semantic analysis on the given program and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, prog: Program) -> Self {
        // Analyze top-level type declarations.
        define_types(ctx, &prog);

        // Analyze top-level function declarations.
        define_fns(ctx, &prog);

        // Analyze each statement in the program.
        let mut analyzed_statements = vec![];
        for statement in prog.statements {
            match statement {
                Statement::FunctionDeclaration(_)
                | Statement::ExternFns(_)
                | Statement::Consts(_)
                | Statement::StructDeclaration(_)
                | Statement::EnumDeclaration(_)
                | Statement::Impl(_) => {
                    // Only include the statement in the output AST if it's not templated.
                    let statement = RichStatement::from(ctx, statement);
                    if !statement.is_templated() {
                        analyzed_statements.push(statement);
                    }
                }
                Statement::Spec(_) => {
                    // We can safely skip specs here because they'll be full analyzed in
                    // `Program::define_fns`.
                }
                other => {
                    ctx.add_err(AnalyzeError::new(
                        ErrorKind::InvalidStatement,
                        "expected type, constant, spec, or function declaration",
                        &other,
                    ));
                }
            }
        }

        // Append all functions that were rendered from templates during analysis to the list
        // of program statements.
        analyzed_statements.extend(ctx.get_rendered_functions_as_statements());

        RichProg {
            statements: analyzed_statements,
        }
    }
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
                if ctx.is_type_or_spec_name_used(struct_type.name.as_str()) {
                    ctx.add_err(AnalyzeError::new(
                        ErrorKind::DuplicateType,
                        format_code!(
                            "another type or spec with the name {} already exists",
                            struct_type.name
                        )
                        .as_str(),
                        struct_type,
                    ));
                    continue;
                }

                ctx.add_extern_struct(struct_type.clone());
            }

            Statement::EnumDeclaration(enum_type) => {
                if ctx.is_type_or_spec_name_used(enum_type.name.as_str()) {
                    ctx.add_err(AnalyzeError::new(
                        ErrorKind::DuplicateType,
                        format_code!(
                            "another type or spec with the name {} already exists",
                            enum_type.name
                        )
                        .as_str(),
                        enum_type,
                    ));
                    continue;
                }

                ctx.add_extern_enum(enum_type.clone());
            }

            Statement::Spec(spec) => {
                if ctx.is_type_or_spec_name_used(spec.name.as_str()) {
                    ctx.add_err(AnalyzeError::new(
                        ErrorKind::DuplicateType,
                        format_code!(
                            "another type or spec with the name {} already exists",
                            spec.name
                        )
                        .as_str(),
                        spec,
                    ));
                    continue;
                }

                ctx.add_extern_spec(spec.clone());
            }

            _ => {}
        }
    }

    // Second pass: Check for type containment cycles.
    let mut results = vec![];
    {
        let extern_structs = ctx.extern_structs();
        for struct_type in extern_structs {
            let result = check_struct_containment_cycles(ctx, struct_type, &mut vec![]);
            results.push((result, struct_type.name.clone()));
        }

        let extern_enums = ctx.extern_enums();
        for enum_type in extern_enums {
            let result = check_enum_containment_cycles(ctx, enum_type, &mut vec![]);
            results.push((result, enum_type.name.clone()));
        }
    }

    // Remove types that have illegal containment cycles from the program context and add them as
    // invalid types instead. We do this so we can safely continue with semantic analysis without
    // having to worry about stack overflows during recursive type resolution.
    for (result, type_name) in results {
        if ctx.consume_error(result).is_none() {
            ctx.remove_extern_struct(type_name.as_str());
            ctx.remove_extern_enum(type_name.as_str());
            ctx.add_invalid_type(type_name.as_str());
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
                analyze_fn_sig(ctx, &func.signature);

                if func.signature.name == "main" {
                    main_defined = true;

                    // Make sure main has no args or return.
                    if func.signature.args.len() != 0 {
                        ctx.add_err(AnalyzeError::new(
                            ErrorKind::InvalidMain,
                            format_code!("function {} cannot have arguments", "main").as_str(),
                            &func.signature,
                        ));
                    }

                    if func.signature.return_type.is_some() {
                        ctx.add_err(AnalyzeError::new(
                            ErrorKind::InvalidMain,
                            format_code!("function {} cannot have a return type", "main").as_str(),
                            &func.signature,
                        ));
                    }
                }

                // If the function is templated, add it to the program context to we can retrieve
                // it whenever we need to render it.
                if func.signature.tmpl_params.is_some() {
                    let rich_fn_sig = RichFnSig::from(ctx, &func.signature);
                    ctx.add_templated_fn(rich_fn_sig.full_name().as_str(), func.clone());
                }
            }

            Statement::ExternFns(ext) => {
                for sig in &ext.fn_sigs {
                    if sig.tmpl_params.is_some() {
                        ctx.add_err(AnalyzeError::new(
                            ErrorKind::InvalidExtern,
                            "extern functions cannot be templated",
                            sig,
                        ));
                        continue;
                    }

                    analyze_fn_sig(ctx, sig);
                }
            }

            Statement::Impl(impl_) => {
                // Set the current impl type ID on the program context so we can access it when
                // resolving type `This`.
                let type_id = TypeId::from(impl_.typ.clone());
                ctx.set_this_type_id(Some(type_id.clone()));

                // Analyze each member function signature and record it as a member of this type
                // in the program context.
                for member_fn in &impl_.member_fns {
                    let fn_sig = RichFnSig::from(ctx, &member_fn.signature);

                    // Make sure this isn't a duplicate member function.
                    if ctx
                        .get_type_member_fn(&type_id, fn_sig.name.as_str())
                        .is_some()
                    {
                        ctx.add_err(AnalyzeError::new(
                            ErrorKind::DuplicateFunction,
                            format_code!(
                                "function {} was already defined for type {}",
                                member_fn.signature.name,
                                type_id
                            )
                            .as_str(),
                            &member_fn.signature,
                        ));
                    } else {
                        // If the member function is templated, add it to the program context so it
                        // can be retrieved and rendered later.
                        if fn_sig.is_templated() {
                            ctx.add_templated_fn(fn_sig.full_name().as_str(), member_fn.clone());
                        }

                        ctx.add_type_member_fn(type_id.clone(), fn_sig);
                    }
                }

                // Remove the current impl type ID from the program context now that we're done
                // checking the function signatures inside the impl block.
                ctx.set_this_type_id(None);
            }

            Statement::Spec(spec) => {
                // Analyze the spec and add it to the program context so we can retrieve and render
                // it later.
                let rich_spec = RichSpec::from(ctx, spec);
                ctx.add_spec(rich_spec);
            }

            _ => {}
        };
    }

    if !main_defined {
        ctx.add_warn(AnalyzeWarning::new_with_default_pos(
            WarnKind::MissingMain,
            "no main function was detected; your code will not execute",
        ));
    }
}
