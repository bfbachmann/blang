use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::closure::{check_closure_returns, RichClosure};
use crate::analyzer::error::{AnalyzeError, AnalyzeResult, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::func_sig::RichFnSig;
use crate::analyzer::prog_context::{ProgramContext, Scope, ScopeKind};
use crate::analyzer::r#type::{check_type_satisfies_spec, RichType, TypeId};
use crate::analyzer::tmpl_params::RichTmplParam;
use crate::format_code;
use crate::parser::func::Function;

/// Represents a semantically valid and type-rich function.
#[derive(PartialEq, Debug, Clone)]
pub struct RichFn {
    pub signature: RichFnSig,
    pub body: RichClosure,
}

impl fmt::Display for RichFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {{...}}", &self.signature)
    }
}

impl RichFn {
    /// Performs semantic analysis on the given function and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, func: Function) -> Self {
        let signature = RichFnSig::from(ctx, &func.signature);

        // If this is a templated function, we'll define
        // Templated functions will be rendered and analyzed when we analyze statements or
        // expressions where they're used. This way, we can use information from the context in
        // which they're used to render and check templated values.
        if func.signature.tmpl_params.is_some() {
            return RichFn {
                signature,
                body: RichClosure::new_empty(),
            };
        }

        // Analyze the function body.
        let rich_closure = RichClosure::from(
            ctx,
            func.body.clone(),
            ScopeKind::FnBody,
            func.signature.args.clone(),
            func.signature.return_type.clone(),
        );

        // Make sure the function return conditions are satisfied by the closure.
        if let Some(ret_type) = &func.signature.return_type {
            let rich_ret_type = RichType::analyze(ctx, &ret_type);
            check_closure_returns(ctx, &rich_closure, &rich_ret_type, &ScopeKind::FnBody);
        }

        RichFn {
            signature,
            body: rich_closure,
        }
    }

    /// Renders the given templated function. Rendering templates is just the process of replacing
    /// parameterized (generic) types with concrete types based on the context in which the
    /// template is being used. The length of `passed_arg_type_ids` should match the number of
    /// arguments for the function and `sig` should be the analyzed signature of `func`.
    pub fn render(
        ctx: &mut ProgramContext,
        sig: &mut RichFnSig,
        func: Function,
        passed_args: &VecDeque<RichExpr>,
    ) -> AnalyzeResult<()> {
        let tmpl_params = match &sig.tmpl_params {
            Some(tp) => tp.params.clone(),
            None => vec![],
        };

        // Create a new template rendering scope and push it onto the stack.
        let scope = Scope::new_tmpl(tmpl_params, sig.ret_type_id.clone());
        ctx.push_scope(scope);

        // Render the function.
        let result = render_fn(ctx, sig, func, passed_args);

        // Pop the scope now that we're done rendering the function.
        ctx.pop_scope();

        result
    }
}

/// Renders a function by replacing template parameters with concrete types and checking that they
/// match the parameter requirements, then analyzing the full function body.
fn render_fn(
    ctx: &mut ProgramContext,
    sig: &mut RichFnSig,
    func: Function,
    passed_args: &VecDeque<RichExpr>,
) -> AnalyzeResult<()> {
    // Iterate through template params and try to resolve each one to a concrete type.
    let mut remapped_type_ids: HashMap<TypeId, TypeId> = HashMap::new();
    if let Some(tmpl_params) = &sig.tmpl_params {
        for param in &tmpl_params.params {
            // Try resolve the concrete type that should be expected in place of this param.
            match resolve_param_type(ctx, sig, passed_args, &param, &remapped_type_ids) {
                Ok(new_type_id) => {
                    let param_type_id = param.get_type_id();
                    remapped_type_ids.insert(param_type_id.clone(), new_type_id.clone());
                }
                Err(err) => {
                    return Err(err);
                }
            };
        }
    }

    // Add the remapped type IDs to the program context so they're also remapped during any
    // type lookups that occur during function analysis.
    for (src_id, dst_id) in &remapped_type_ids {
        ctx.add_type_id_remapping(src_id.clone(), dst_id.clone());
    }

    // Check that the values passed as function arguments have the right types.
    check_fn_arg_types(ctx, sig, passed_args, &remapped_type_ids)?;

    // Check that the function returns the expected type.
    check_ret_type(ctx, sig, &remapped_type_ids)?;

    // Make the required type ID replacements in the function signature.
    {
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

    // Now that all template parameters have been substituted with concrete types, analyze the
    // function and add the result to the program context.
    {
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

        // Change the function signature name to its fully resolved name (with type info).
        sig.name = sig.full_name();

        // Drop the now-useless template parameters.
        sig.tmpl_params = None;

        // Recompute the type ID, since the signature has changed. This type ID is guaranteed
        // to be unique to this rendered function because it is created from the function name
        // which will contain characters that are illegal in identifiers.
        sig.type_id = TypeId::new_unresolved(sig.name.as_str());

        // Add the rendered function as a resolved type with the new type ID so it can be
        // looked up later.
        ctx.add_resolved_type(sig.type_id.clone(), RichType::from_fn_sig(sig.clone()));

        // Add the rendered function to the program context so it can be included in the AST
        // later.
        ctx.add_rendered_fn(RichFn {
            signature: sig.clone(),
            body: rich_closure,
        });
    };

    Ok(())
}

/// Checks that each passed argument has the expected type as defined in the function signature.
fn check_fn_arg_types(
    ctx: &mut ProgramContext,
    sig: &RichFnSig,
    passed_args: &VecDeque<RichExpr>,
    remapped_type_ids: &HashMap<TypeId, TypeId>,
) -> AnalyzeResult<()> {
    // Make a copy of the original function signature so we can print it unedited into error
    // messages.
    let original_fn_sig = sig.clone();

    // Check that all the passed arguments match the template requirements and substitute
    // concrete types for templated argument types.
    for (defined_arg, passed_arg) in sig.args.iter().zip(passed_args.iter()) {
        // Skip checks if the type is unknown (i.e. already failed analysis).
        let passed_type = ctx.must_get_resolved_type(&passed_arg.type_id);
        if passed_type.is_unknown() {
            continue;
        }

        // Find the expected type for this argument as defined in the function signature (and
        // perform type ID remapping if necessary).
        let expected_type = match remapped_type_ids.get(&defined_arg.type_id) {
            Some(remapped_type_id) => ctx.must_get_resolved_type(remapped_type_id),
            None => ctx.must_get_resolved_type(&defined_arg.type_id),
        };

        if !passed_type.is_same_as(expected_type, remapped_type_ids) {
            let mut err = AnalyzeError::new(
                ErrorKind::MismatchedTypes,
                format_code!(
                    "cannot use value of type {} as argument {} to templated function {}",
                    passed_type,
                    format!("{}: {}", defined_arg.name, expected_type),
                    original_fn_sig,
                )
                .as_str(),
                passed_arg,
            );

            // Let the user know if their argument type has changed because it is a template
            // parameter that has been rendered as a specific concrete type.
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
    remapped_type_ids: &HashMap<TypeId, TypeId>,
) -> AnalyzeResult<()> {
    // Return early if there is no return type.
    if sig.ret_type_id.is_none() {
        return Ok(());
    }

    // Return early if the return type is not templated.
    #[allow(dead_code)]
    let ret_type_id = sig.ret_type_id.as_ref().unwrap();

    #[allow(unused_variables)]
    let ret_type = match remapped_type_ids.get(&ret_type_id) {
        Some(remapped_type_id) => ctx.must_get_resolved_type(remapped_type_id),
        None => ctx.must_get_resolved_type(ret_type_id),
    };

    // TODO: Check that the return type is what is expected.

    Ok(())
}

/// Tries to resolve and return the type ID of the concrete type that should take the place of
/// `param` in the function signature using the passed arguments. If resolved, maps the param
/// type ID to the resolved concrete type in the Program context and returns the resolved type ID.
fn resolve_param_type<'a>(
    ctx: &'a mut ProgramContext,
    sig: &'a RichFnSig,
    passed_args: &'a VecDeque<RichExpr>,
    param: &'a RichTmplParam,
    remapped_type_ids: &'a HashMap<TypeId, TypeId>,
) -> AnalyzeResult<&'a TypeId> {
    // Find the concrete type that should be expected in place of this parameterized type.
    let passed_arg = match find_passed_arg_for_param(sig, passed_args, param) {
        Ok(arg) => arg,
        Err(err) => return Err(err),
    };

    // Now check that the concrete type used in place of the template parameter actually meets the
    // parameter's requirements.
    if let Err(err) = check_arg_type_for_param(ctx, passed_arg, param, remapped_type_ids) {
        return Err(err);
    }

    // Map this param type ID to the concrete type we found so we can resolve the concrete type
    // wherever this param is used in the function.
    let concrete_type = ctx.must_get_resolved_type(&passed_arg.type_id);
    ctx.add_resolved_type(param.get_type_id(), concrete_type.clone());
    Ok(&passed_arg.type_id)
}

/// Tries to find the concrete type to use in place of `param`.
fn find_passed_arg_for_param<'a>(
    sig: &'a RichFnSig,
    passed_args: &'a VecDeque<RichExpr>,
    param: &'a RichTmplParam,
) -> AnalyzeResult<&'a RichExpr> {
    let param_type_id = param.get_type_id();

    // Find the first argument that uses this template param.
    for (defined_arg, passed_arg) in sig.args.iter().zip(passed_args.iter()) {
        if defined_arg.type_id == param_type_id {
            return Ok(passed_arg);
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

/// Checks that `passed_arg` has a type that satisfies the requirements of `param`.
fn check_arg_type_for_param<'a>(
    ctx: &'a ProgramContext,
    passed_arg: &'a RichExpr,
    param: &'a RichTmplParam,
    remapped_type_ids: &'a HashMap<TypeId, TypeId>,
) -> AnalyzeResult<()> {
    let passed_type = ctx.must_get_resolved_type(&passed_arg.type_id);

    if let Some(expected_type_id) = &param.required_type_id {
        // This is a template parameter that is just an alias for a concrete type, so make
        // sure the passed argument is of that required type.
        let expected_type = match ctx.must_get_resolved_type(expected_type_id) {
            // Resolve the templated type.
            RichType::Templated(param) => ctx.must_get_resolved_type(&param.get_type_id()),

            // The type is not templated, so just return it.
            not_templated => not_templated,
        };

        if !passed_type.is_same_as(expected_type, remapped_type_ids) {
            return Err(AnalyzeError::new(
                ErrorKind::MismatchedTypes,
                format_code!(
                    "expected argument type {} (in place of parameter {}), but found {}",
                    expected_type,
                    param,
                    passed_type,
                )
                .as_str(),
                passed_arg,
            ));
        }
    } else {
        // This is a template parameter that requires that the type used in its place
        // implements a set of specs, so make sure the passed argument type implements those
        // specs.
        for spec_name in &param.required_spec_names {
            let spec = ctx.get_spec(spec_name).unwrap();
            if let Err(err_msg) = check_type_satisfies_spec(ctx, &passed_arg.type_id, spec) {
                return Err(AnalyzeError::new(
                    ErrorKind::SpecNotSatisfied,
                    format_code!(
                        "argument has type {} which doesn't satisfy spec {}",
                        passed_type,
                        spec.name,
                    )
                    .as_str(),
                    passed_arg,
                )
                .with_detail(err_msg.as_str()));
            }
        }
    }

    Ok(())
}
