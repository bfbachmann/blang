use std::collections::HashMap;

use crate::analyzer::ast::func::{analyze_fn_sig, AFnSig};
use crate::analyzer::ast::spec::ASpecType;
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_containment::{check_enum_containment, check_struct_containment};
use crate::parser::ast::ext::Extern;
use crate::parser::ast::func::Function;
use crate::parser::ast::r#impl::Impl;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::spec::Spec;
use crate::parser::ast::statement::Statement;
use crate::parser::module::Module;

/// Represents a semantically analyzed source file.
#[derive(Debug)]
pub struct AModule {
    pub path: String,
    pub statements: Vec<AStatement>,
}

impl AModule {
    /// Performs semantic analysis on the given module and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, module: &Module) -> AModule {
        // Set the current mod path in the program context so it can be used to
        // create unique identifiers for symbols in this module during analysis.
        ctx.set_cur_mod(&module);

        // Analyze the module now that dependencies have all been analyzed.
        // First pass: define types and functions in the module without analyzing them yet.
        define_consts(ctx, module);
        define_types(ctx, module);
        define_specs(ctx, module);
        define_fns(ctx, module);

        // Second pass: fully analyze all program statements.
        let mut analyzed_statements = vec![];
        for statement in &module.statements {
            match statement {
                Statement::FunctionDeclaration(_)
                | Statement::ExternFn(_)
                | Statement::Const(_)
                | Statement::StructDeclaration(_)
                | Statement::EnumDeclaration(_)
                | Statement::Impl(_) => {
                    let statement = AStatement::from(ctx, &statement);
                    analyzed_statements.push(statement);
                }

                Statement::SpecDeclaration(_) => {
                    // We can safely skip specs here because they'll be full analyzed in
                    // `analyze_specs`.
                }

                Statement::Use(_) => {
                    // We can skip `use` statements since they're handled in `analyze_module`.
                }

                other => {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::InvalidStatement,
                        "expected use, type, constant, spec, or function declaration",
                        other,
                    ));
                }
            }
        }

        AModule {
            path: module.path.clone(),
            statements: analyzed_statements,
        }
    }
}

/// Defines top-level types and specs in the program context without deeply analyzing their fields,
/// so they can be referenced later. This will simply check for type name collisions and
/// containment cycles. We do this before fully analyzing types to prevent infinite recursion.
fn define_types(ctx: &mut ProgramContext, module: &Module) {
    // First pass: Define all types without analyzing their fields. In this pass, we will only
    // check that there are no type name collisions.
    for statement in &module.statements {
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
        let unchecked_structs = ctx.unchecked_struct_types();
        for struct_type in unchecked_structs {
            let result = check_struct_containment(ctx, struct_type, &mut vec![]);
            results.push((result, struct_type.name.clone()));
        }

        let unchecked_enums = ctx.unchecked_enum_types();
        for enum_type in unchecked_enums {
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
            ctx.insert_invalid_type_name(type_name);
        }
    }
}

/// Stores un-analyzed constant declarations in the program context
/// so they can be fetched and analyzed later when they're used.
fn define_consts(ctx: &mut ProgramContext, module: &Module) {
    for statement in &module.statements {
        if let Statement::Const(const_decl) = statement {
            ctx.try_insert_unchecked_const(const_decl.clone());
        }
    }
}

/// Analyzes all specs declared in the module.
fn define_specs(ctx: &mut ProgramContext, module: &Module) {
    for statement in &module.statements {
        match statement {
            Statement::SpecDeclaration(spec) => {
                define_spec(ctx, spec);
            }
            _ => {}
        }
    }
}

/// Analyzes all top-level function signatures (this includes those inside specs) and defines them
/// in the program context so they can be referenced later. This will not perform any analysis of
/// function bodies.
fn define_fns(ctx: &mut ProgramContext, module: &Module) {
    for statement in &module.statements {
        match statement {
            Statement::FunctionDeclaration(func) => {
                define_fn(ctx, func);
            }

            Statement::ExternFn(ext) => {
                define_extern_fn(ctx, ext);
            }

            Statement::Impl(impl_) => {
                define_impl(ctx, impl_);
            }

            _ => {}
        };
    }
}

fn define_fn(ctx: &mut ProgramContext, func: &Function) {
    analyze_fn_sig(ctx, &func.signature);

    if func.signature.name == "main" {
        if let Some(params) = &func.signature.params {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::InvalidMain,
                format_code!("function {} cannot have parameters", "main").as_str(),
                params,
            ));
        }

        if !func.signature.args.is_empty() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::InvalidMain,
                format_code!("function {} cannot take arguments", "main").as_str(),
                func.signature.args.get(0).unwrap(),
            ));
        }

        if let Some(ret_type) = &func.signature.maybe_ret_type {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::InvalidMain,
                format_code!("function {} cannot have a return type", "main").as_str(),
                ret_type,
            ));
        }
    }
}

fn define_extern_fn(ctx: &mut ProgramContext, ext: &Extern) {
    if ext.fn_sig.params.is_some() {
        ctx.insert_err(AnalyzeError::new(
            ErrorKind::InvalidExtern,
            "external functions cannot be generic",
            &ext.fn_sig,
        ));
        return;
    }

    analyze_fn_sig(ctx, &ext.fn_sig);

    // Record the extern function name as public in the current module if necessary.
    if ext.is_pub {
        ctx.insert_pub_fn_name(ext.fn_sig.name.as_str());
    }
}

fn define_impl(ctx: &mut ProgramContext, impl_: &Impl) {
    // Set the current impl type key on the program context so we can access it when
    // resolving type `Self`.
    let impl_type_key = ctx.resolve_maybe_polymorphic_type(&Type::Unresolved(impl_.typ.clone()));

    // Skip the impl if it's illegal.
    if !ctx.type_declared_in_cur_mod(impl_type_key) {
        return;
    }

    // If there are parameters for this impl, push them to the program context
    // so we can resolve them when we're analyzing member functions.
    let typ = ctx.must_get_type(impl_type_key);
    let has_params = match typ.params() {
        Some(params) => {
            ctx.push_params(params.clone());
            true
        }
        None => false,
    };

    ctx.set_cur_self_type_key(Some(impl_type_key));

    let is_default_impl = impl_.maybe_spec.is_none();

    // Analyze each member function signature.
    let mut fn_type_keys = HashMap::new();
    for member_fn in &impl_.member_fns {
        let fn_sig = AFnSig::from(ctx, &member_fn.signature);

        // Make sure there are no other functions in this impl block that share the same name.
        if fn_type_keys.contains_key(fn_sig.name.as_str()) {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::DuplicateFunction,
                format_code!(
                    "function {} already defined in this {}",
                    member_fn.signature.name,
                    "impl",
                )
                .as_str(),
                &member_fn.signature,
            ));

            // Skip invalid func.
            continue;
        }

        // If this is a default impl (i.e. it's not implementing a spec), then we need to
        // make sure that function names don't collide with those of existing functions from
        // other default impls on this type.
        if is_default_impl {
            let has_matching_default_fn = ctx
                .get_default_member_fn(impl_type_key, fn_sig.name.as_str())
                .is_some();
            if has_matching_default_fn {
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::DuplicateFunction,
                    format_code!(
                        "function {} already defined for type {}",
                        fn_sig.name,
                        ctx.display_type(impl_type_key),
                    )
                    .as_str(),
                    &member_fn.signature,
                ));

                // Skip invalid func.
                continue;
            }
        }

        fn_type_keys.insert(fn_sig.name.clone(), fn_sig.type_key);
    }

    ctx.set_cur_self_type_key(None);

    if has_params {
        ctx.pop_params();
    }

    // Regardless of errors, we'll mark this `impl` as implementing the
    // spec it claims it does. This is just to prevent redundant error
    // messages when the corresponding type gets used.
    let maybe_spec_tk = match &impl_.maybe_spec {
        Some(spec) => 'check: {
            // Try to find the analyzed spec type. It might not be there if it has not
            // yet been analyzed.
            if let Some(spec_type_key) =
                ctx.get_type_key_by_type_name(spec.maybe_mod_name.as_ref(), spec.name.as_str())
            {
                break 'check Some(spec_type_key);
            }

            // Try to find the un-analyzed spec type and analyze it.
            if spec.maybe_mod_name.is_none() {
                if let Some(unchecked_spec) = ctx.get_unchecked_spec(spec.name.as_str()) {
                    ASpecType::from(ctx, &unchecked_spec.clone());
                    let spec_type_key = ctx
                        .get_type_key_by_type_name(None, spec.name.as_str())
                        .unwrap();
                    break 'check Some(spec_type_key);
                }
            }

            ctx.insert_err(AnalyzeError::new(
                ErrorKind::UndefSpec,
                format_code!("spec {} not defined", spec.name).as_str(),
                spec,
            ));

            return;
        }

        None => None,
    };

    ctx.insert_impl(impl_type_key, maybe_spec_tk, fn_type_keys);
}

fn define_spec(ctx: &mut ProgramContext, spec: &Spec) {
    // Make sure this spec name is not a duplicate.
    if ctx.get_spec_type(None, spec.name.as_str()).is_some() {
        ctx.insert_err(AnalyzeError::new(
            ErrorKind::DuplicateSpec,
            format_code!("another spec named {} already exists", spec.name).as_str(),
            spec,
        ));

        return;
    }

    // Analyze the spec and add it to the program context so we can retrieve it later.
    ASpecType::from(ctx, spec);
}
