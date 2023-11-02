use std::collections::{HashMap, VecDeque};

use colored::Colorize;

use crate::analyzer::closure::{check_closure_returns, RichClosure};
use crate::analyzer::error::{AnalyzeError, AnalyzeResult, ErrorKind};
use crate::analyzer::expr::{RichExpr, RichExprKind};
use crate::analyzer::func::RichFn;
use crate::analyzer::func_sig::RichFnSig;
use crate::analyzer::prog_context::{ProgramContext, Scope, ScopeKind};
use crate::analyzer::r#type::{check_type_satisfies_spec, RichType, TypeId};
use crate::analyzer::symbol::RichSymbol;
use crate::analyzer::tmpl_params::RichTmplParam;
use crate::format_code;
use crate::parser::func::Function;

/// Renders the given templated function. Rendering templates is just the process of replacing
/// parameterized (generic) types with concrete types based on the context in which the
/// template is being used. The length of `passed_arg_tids` should match the number of
/// arguments for the function and `sig` should be the analyzed signature of `func`.
/// If `maybe_passed_args` is provided, it should be the arguments to the given function, and must
/// have the right length. After rendering completes, the arguments in `maybe_passed_args` will be
/// coerced to their required types.
pub fn render_fn_tmpl(
    ctx: &mut ProgramContext,
    sig: &mut RichFnSig,
    func: Function,
    passed_arg_tids: &Vec<TypeId>,
    maybe_expected_ret_tid: Option<&TypeId>,
    maybe_passed_args: Option<&mut VecDeque<RichExpr>>,
) -> AnalyzeResult<()> {
    let tmpl_params = match &sig.tmpl_params {
        Some(tp) => tp.params.clone(),
        None => vec![],
    };

    // Create a new template rendering scope and push it onto the stack.
    let scope = Scope::new_tmpl(tmpl_params, sig.ret_type_id.clone());
    ctx.push_scope(scope);

    // Render the function.
    let result = render_fn(ctx, sig, func, passed_arg_tids, maybe_expected_ret_tid);

    // If rendering succeeded and argument expressions were given, try coerce them to the
    // newly-rendered types.
    if result.is_ok() {
        if let Some(passed_args) = maybe_passed_args {
            for (i, defined_arg) in sig.args.iter().enumerate() {
                let defined_type = ctx.must_get_resolved_type(&defined_arg.type_id).clone();
                let passed_arg = passed_args.remove(i).unwrap();
                let coerced_arg = passed_arg.try_coerce_to(ctx, &defined_type);
                passed_args.insert(i, coerced_arg);
            }
        }
    }

    // Pop the scope now that we're done rendering the function.
    ctx.pop_scope();

    if let Err(err) = result {
        return Err(err);
    }

    // Add the rendered function as a resolved type with the new type ID so it can be
    // looked up later.
    ctx.add_rendered_type(sig.type_id.clone(), RichType::from_fn_sig(sig.clone()));

    // Add the rendered function to the program context so it can be included in the AST
    // later.
    ctx.add_rendered_fn(RichFn {
        signature: sig.clone(),
        body: result.unwrap(),
    });

    Ok(())
}

/// Renders the given templated function signature. Rendering templates is just the process of
/// replacing parameterized (generic) types with concrete types based on the context in which the
/// template is being used. The length of `passed_arg_tids` should match the number of
/// arguments for the function.
pub fn render_fn_sig_tmpl(
    ctx: &mut ProgramContext,
    sig: &mut RichFnSig,
    passed_arg_tids: &Vec<TypeId>,
    maybe_expected_ret_tid: Option<&TypeId>,
) -> AnalyzeResult<()> {
    let tmpl_params = match &sig.tmpl_params {
        Some(tp) => tp.params.clone(),
        None => vec![],
    };

    // Create a new template rendering scope and push it onto the stack.
    let scope = Scope::new_tmpl(tmpl_params, sig.ret_type_id.clone());
    ctx.push_scope(scope);

    // Render the function.
    let result = render_fn_sig(ctx, sig, passed_arg_tids, maybe_expected_ret_tid);

    // Pop the scope now that we're done rendering the function.
    ctx.pop_scope();

    if let Err(err) = result {
        return Err(err);
    }

    // Add the rendered function as a resolved type with the new type ID so it can be
    // looked up later.
    ctx.add_rendered_type(sig.type_id.clone(), RichType::from_fn_sig(sig.clone()));

    Ok(())
}

/// Renders a function by replacing template parameters with concrete types and checking that they
/// match the parameter requirements, then analyzing the full function body.
fn render_fn(
    ctx: &mut ProgramContext,
    sig: &mut RichFnSig,
    func: Function,
    passed_arg_tids: &Vec<TypeId>,
    maybe_expected_ret_tid: Option<&TypeId>,
) -> AnalyzeResult<RichClosure> {
    render_fn_sig(ctx, sig, passed_arg_tids, maybe_expected_ret_tid)?;

    // Now that all template parameters have been substituted with concrete types, analyze the
    // function and add the result to the program context.
    let body = render_fn_body(ctx, sig, func);
    Ok(body)
}

/// Renders the function signature by replacing template parameters with concrete types.
fn render_fn_sig(
    ctx: &mut ProgramContext,
    sig: &mut RichFnSig,
    passed_arg_tids: &Vec<TypeId>,
    maybe_expected_ret_tid: Option<&TypeId>,
) -> AnalyzeResult<()> {
    // Iterate through template params and try to resolve each one to a concrete type.
    if let Some(tmpl_params) = &sig.tmpl_params {
        for param in &tmpl_params.params {
            // Try resolve the concrete type that should be expected in place of this param.
            match resolve_param_type(ctx, sig, passed_arg_tids, maybe_expected_ret_tid, &param) {
                Ok(new_type_id) => {
                    let param_type_id = param.get_type_id();
                    ctx.add_type_id_remapping(param_type_id.clone(), new_type_id.clone());
                }
                Err(err) => {
                    return Err(err);
                }
            };
        }
    }

    // Check that the values passed as function arguments have the right types.
    check_fn_arg_types(ctx, sig, passed_arg_tids)?;

    // Check that the function returns the expected type.
    check_ret_type(ctx, sig, maybe_expected_ret_tid)?;

    // Make the required type ID replacements in the function signature.
    replace_type_ids(sig, ctx.get_remapped_type_ids().unwrap());

    // Change the function signature name to its fully resolved name (with type info).
    sig.name = sig.full_name();

    // Drop the now-useless template parameters.
    sig.tmpl_params = None;

    // Recompute the type ID, since the signature has changed. This type ID is guaranteed
    // to be unique to this rendered function because it is created from the function name
    // which will contain characters that are illegal in identifiers.
    sig.type_id = TypeId::new_unresolved(sig.name.as_str());

    Ok(())
}

/// Renders the function body by replacing template parameters with concrete types and performing
/// normal analysis on the rendered function body.
fn render_fn_body(ctx: &mut ProgramContext, sig: &mut RichFnSig, func: Function) -> RichClosure {
    let rich_closure = RichClosure::from_analyzed(
        ctx,
        func.body,
        ScopeKind::FnBody,
        sig.args.clone(),
        sig.ret_type_id.clone(),
    );

    // Make sure the function return conditions are satisfied by the closure.
    if let Some(ret_type) = &func.signature.return_type {
        let rich_ret_type = RichType::analyze(ctx, &ret_type);
        check_closure_returns(ctx, &rich_closure, &rich_ret_type, &ScopeKind::FnBody);
    }

    rich_closure
}

/// Checks that each passed argument has the expected type as defined in the function signature.
fn check_fn_arg_types(
    ctx: &mut ProgramContext,
    sig: &RichFnSig,
    passed_arg_tids: &Vec<TypeId>,
) -> AnalyzeResult<()> {
    // Make a copy of the original function signature so we can print it unedited into error
    // messages.
    let original_fn_sig = sig.clone();

    // Check that all the passed arguments match the template requirements and substitute
    // concrete types for templated argument types.
    for (defined_arg, passed_arg_tid) in sig.args.iter().zip(passed_arg_tids.iter()) {
        // Skip checks if the type is unknown (i.e. already failed analysis).
        let passed_type = ctx.must_get_resolved_type(passed_arg_tid);
        if passed_type.is_unknown() {
            continue;
        }

        // Find the expected type for this argument as defined in the function signature (and
        // perform type ID remapping if necessary).
        let expected_type = ctx.must_get_resolved_type(&defined_arg.type_id);

        match passed_type {
            RichType::Function(passed_fn_sig) if passed_fn_sig.is_templated() => {
                let symbol_expr = RichExpr::new(
                    RichExprKind::Symbol(RichSymbol::new_with_default_pos(
                        passed_fn_sig.name.as_str(),
                        passed_fn_sig.type_id.clone(),
                        None,
                    )),
                    passed_fn_sig.type_id.clone(),
                );

                // If the type rendering and coercion fails, an error will be placed in the
                // program context. Otherwise, the types are compatible and there is no need
                // for further type checking.
                let expected_type = expected_type.clone();
                symbol_expr.try_coerce_to(ctx, &expected_type);
                return Ok(());
            }
            _ => {}
        }

        if !passed_type.is_same_as(ctx, &expected_type) {
            let mut err = AnalyzeError::new_with_default_pos(
                ErrorKind::MismatchedTypes,
                format_code!(
                    "cannot use value of type {} as argument {} to templated function {}",
                    passed_type,
                    format!("{}: {}", defined_arg.name, expected_type),
                    original_fn_sig,
                )
                .as_str(),
            );

            // Let the user know if their argument type has changed because it is a template
            // parameter that has been rendered as a specific concrete type.
            let expected_type = expected_type.clone();
            let remapped_type_ids = ctx.get_remapped_type_ids().unwrap();
            if remapped_type_ids.contains_key(&defined_arg.type_id) {
                err = err.with_detail(
                    format_code!(
                        "Type {} is expected in place of template parameter {} for argument {} in \
                        this call.",
                        expected_type,
                        defined_arg.type_id,
                        defined_arg.name,
                    )
                    .as_str(),
                )
            }

            return Err(err);
        }
    }

    Ok(())
}

/// Checks that the function returns the expected type.
fn check_ret_type(
    ctx: &ProgramContext,
    sig: &RichFnSig,
    maybe_expected_ret_tid: Option<&TypeId>,
) -> AnalyzeResult<()> {
    if maybe_expected_ret_tid.is_none() {
        return Ok(());
    }

    if sig.ret_type_id.is_none() {
        return Err(AnalyzeError::new_with_default_pos(
            ErrorKind::ExpectedReturnValue,
            format_code!(
                "{} has no return type, but was used in a context where one is expected",
                sig
            )
            .as_str(),
        ));
    }

    let expected_tid = maybe_expected_ret_tid.unwrap();
    let actual_tid = sig.ret_type_id.as_ref().unwrap();
    let expected_type = ctx.must_get_resolved_type(expected_tid);
    let actual_type = ctx.must_get_resolved_type(actual_tid);

    // Only do the type check if neither type failed analysis.
    let skip_check = expected_type.is_unknown() || actual_type.is_unknown();
    if !skip_check && !actual_type.is_same_as(ctx, expected_type) {
        return Err(AnalyzeError::new_with_default_pos(
            ErrorKind::MismatchedTypes,
            format_code!(
                "expected return type {}, but found {}",
                expected_type,
                actual_type
            )
            .as_str(),
        ));
    }

    Ok(())
}

/// Tries to resolve and return the type ID of the concrete type that should take the place of
/// `param` in the function signature using the passed arguments and expected return type. If
/// resolved, maps the param  type ID to the resolved concrete type in the Program context and
/// returns the resolved type ID.
fn resolve_param_type<'a>(
    ctx: &'a mut ProgramContext,
    sig: &'a RichFnSig,
    passed_arg_tids: &'a Vec<TypeId>,
    maybe_expected_ret_tid: Option<&'a TypeId>,
    param: &'a RichTmplParam,
) -> AnalyzeResult<TypeId> {
    // Check if we can convert the param required type to a concrete type by just replacing its
    // type IDs.
    if let Some(param_req_tid) = &param.required_type_id {
        return Ok(param_req_tid.clone());
    }

    // Find the concrete type that is being used in place of this parameterized type.
    let resolved_tid =
        get_type_used_for_param(ctx, sig, passed_arg_tids, maybe_expected_ret_tid, param)?;

    // Now check that the concrete type used in place of the template parameter actually meets the
    // parameter's requirements.
    if let Err(err) = check_type_used_for_param(ctx, &resolved_tid, param) {
        return Err(err);
    }

    // Map this param type ID to the concrete type we found so we can resolve the concrete type
    // wherever this param is used in the function.
    let concrete_type = ctx.must_get_resolved_type(&resolved_tid);
    ctx.add_resolved_type(param.get_type_id(), concrete_type.clone());
    Ok(resolved_tid)
}

/// Tries to find the concrete type used in place of `param`.
fn get_type_used_for_param<'a>(
    ctx: &'a mut ProgramContext,
    sig: &'a RichFnSig,
    passed_arg_tids: &'a Vec<TypeId>,
    maybe_expected_ret_tid: Option<&'a TypeId>,
    param: &'a RichTmplParam,
) -> AnalyzeResult<TypeId> {
    let param_type_id = param.get_type_id();

    // Try find the first argument that uses this template param.
    for (defined_arg, passed_tid) in sig.args.iter().zip(passed_arg_tids.iter()) {
        if defined_arg.type_id == param_type_id {
            return Ok(passed_tid.clone());
        }
    }

    // There is no argument that has this param as its type, so check if it's the return
    // type.
    if let Some(ret_tid) = &sig.ret_type_id {
        let ret_type = ctx.must_get_resolved_type(ret_tid);
        if let RichType::Templated(ret_param) = ret_type {
            if ret_param.name == param.name {
                if let Some(tid) = maybe_expected_ret_tid {
                    return Ok(tid.clone());
                };
            }
        }
    }

    // Error because at this point we were able to resolve the concrete type used or expected in
    // place of this param.
    Err(AnalyzeError::new(
        ErrorKind::UnresolvedTmplParams,
        format_code!(
            "parameter {} on templated function {} could not be resolved to a concrete type",
            param_type_id,
            sig,
        )
        .as_str(),
        param,
    )
    .with_help("Consider adding type annotations to this function call."))
}

/// Checks that `resolved_tid` has a type that satisfies the requirements of `param`.
fn check_type_used_for_param<'a>(
    ctx: &'a mut ProgramContext,
    resolved_tid: &'a TypeId,
    param: &'a RichTmplParam,
) -> AnalyzeResult<()> {
    let resolved_type = ctx.must_get_resolved_type(resolved_tid).clone();

    if let Some(expected_type_id) = &param.required_type_id {
        // This is a template parameter that is just an alias for a concrete type, so make
        // sure the passed argument is of that required type.
        let expected_type = match ctx.must_get_resolved_type(expected_type_id) {
            // Resolve the templated type.
            RichType::Templated(param) => ctx.must_get_resolved_type(&param.get_type_id()),

            // The type is not templated, so just return it.
            not_templated => not_templated,
        };

        if !resolved_type.is_same_as(ctx, expected_type) {
            return Err(AnalyzeError::new_with_default_pos(
                ErrorKind::MismatchedTypes,
                format_code!(
                    "expected argument type {} (in place of parameter {}), but found {}",
                    expected_type,
                    param,
                    resolved_type,
                )
                .as_str(),
            ));
        }
    } else {
        // This is a template parameter that requires that the type used in its place
        // implements a set of specs, so make sure the passed argument type implements those
        // specs.
        for spec_name in &param.required_spec_names {
            let spec = ctx.get_spec(spec_name).unwrap().clone();
            if let Err(err_msg) = check_type_satisfies_spec(ctx, resolved_tid, &spec) {
                return Err(AnalyzeError::new_with_default_pos(
                    ErrorKind::SpecNotSatisfied,
                    format_code!(
                        "argument has type {} which doesn't satisfy spec {}",
                        resolved_type,
                        spec.name,
                    )
                    .as_str(),
                )
                .with_detail(err_msg.as_str()));
            }
        }
    }

    Ok(())
}

/// Replaces type IDs in `sig` using the mappings in `remapped_type_ids`.
fn replace_type_ids(sig: &mut RichFnSig, remapped_type_ids: &HashMap<TypeId, TypeId>) {
    for arg in sig.args.iter_mut() {
        if let Some(new_type_id) = remapped_type_ids.get(&arg.type_id) {
            arg.type_id = new_type_id.clone();
        }
    }

    if let Some(ret_type_id) = &mut sig.ret_type_id {
        if let Some(new_type_id) = remapped_type_ids.get(ret_type_id) {
            sig.ret_type_id = Some(new_type_id.clone());
        }
    }
}
