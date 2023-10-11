use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::closure::{check_closure_returns, RichClosure};
use crate::analyzer::error::{AnalyzeError, AnalyzeResult, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::func_sig::RichFnSig;
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::r#type::{check_type_satisfies_spec, RichType, TypeId};
use crate::format_code;
use crate::parser::func::Function;
use crate::parser::r#type::Type;

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

        // Avoid any further analysis if the function is templated. Templated functions will be
        // rendered and analyzed when we analyze statements or expressions where they're used. This
        // way, we can use information from the context in which they're used to render and check
        // templated values.
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
        // Define templated types in the program context to prevent them from being resolved as
        // existing concrete types with the same names.
        let mut shadowed_type_mappings = HashMap::new();
        let mut type_ids_to_delete = vec![];
        if let Some(tmpl_params) = &sig.tmpl_params {
            for (name, param) in &tmpl_params.params {
                let param_type_id = TypeId::from(Type::new_unknown(name.as_str()));
                let templated_type = RichType::Templated(param.clone());

                match ctx.add_resolved_type(param_type_id.clone(), templated_type) {
                    Some(existing_type) => {
                        shadowed_type_mappings.insert(param_type_id, existing_type);
                    }
                    None => {
                        type_ids_to_delete.push(param_type_id);
                    }
                };
            }
        }

        // Check that all the passed arguments match the template requirements and substitute
        // concrete types for templated argument types.
        for (defined_arg, passed_arg) in sig.args.iter_mut().zip(passed_args.iter()) {
            let defined_type = ctx.get_resolved_type(&defined_arg.type_id).unwrap();
            let passed_type = ctx.get_resolved_type(&passed_arg.type_id).unwrap();

            // Skip checks if the type is unknown (i.e. already failed analysis).
            if passed_type.is_unknown() {
                return Ok(());
            }

            // If the argument type in the function signature is a template parameter (a generic),
            // make sure the passed argument type satisfies the parameter's requirements.
            if let RichType::Templated(tmpl_param) = defined_type {
                if let Some(expected_type_id) = &tmpl_param.required_type_id {
                    let expected_type = ctx.get_resolved_type(expected_type_id).unwrap();
                    if !passed_type.is_same_as(expected_type) {
                        return Err(AnalyzeError::new(
                            ErrorKind::MismatchedTypes,
                            format_code!(
                                "expected argument type {} (in place of parameter {}), but found {}",
                                expected_type,
                                tmpl_param,
                                passed_type,
                            )
                            .as_str(),
                            passed_arg,
                        )
                        .with_detail(
                            format_code!(
                                "Argument {} on function {} uses template \
                                parameter {} which requires type {}.",
                                defined_arg.name,
                                sig,
                                tmpl_param.name,
                                expected_type
                            )
                            .as_str(),
                        ));
                    }
                } else {
                    for spec_name in &tmpl_param.required_spec_names {
                        // TODO: Is the spec guaranteed to be defined at this point?
                        let spec = ctx.get_spec(spec_name).unwrap();
                        if let Err(err_msg) =
                            check_type_satisfies_spec(ctx, &passed_arg.type_id, spec)
                        {
                            return Err(AnalyzeError::new(
                                ErrorKind::SpecNotSatisfied,
                                format_code!(
                                    "type {} doesn't satisfy spec {}",
                                    passed_type,
                                    spec.name
                                )
                                .as_str(),
                                passed_arg,
                            )
                            .with_detail(err_msg.as_str()));
                        }
                    }
                }

                // Add the mapping from the templated type ID to the passed argument type so we
                // can resolved this templated type when rendering the function.
                let param_type_id = TypeId::from(Type::new_unknown(tmpl_param.name.as_str()));
                ctx.add_resolved_type(param_type_id.clone(), passed_type.clone());

                // Replace all argument and return types that use this template param in the
                // function signature.
                defined_arg.type_id = passed_arg.type_id.clone();
            } else if !passed_type.is_same_as(defined_type) {
                return Err(AnalyzeError::new(
                    ErrorKind::MismatchedTypes,
                    format_code!(
                        "expected argument type {}, but found {}",
                        defined_type,
                        passed_type
                    )
                    .as_str(),
                    passed_arg,
                ));
            }
        }

        // Render the return type.
        if sig.ret_type_id.is_some() {
            // If the return type is templated and it uses a template param that we've already
            // resolved, we just need to replace the templated return type with the already-resolved
            // concrete type.
            // TODO

            // If we have not resolved the template param used as the return type, we need to infer
            // its type from the context in which it is called.
            // TODO
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
            sig.type_id = TypeId::from(Type::new_unknown(sig.name.as_str()));

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

        // Restore old type mappings that we overwrote with template parameters.
        for (type_id, shadowed_type) in shadowed_type_mappings {
            ctx.add_resolved_type(type_id, shadowed_type);
        }

        // Delete type mappings for template parameters.
        for to_delete in type_ids_to_delete {
            ctx.remove_resolved_type(&to_delete);
        }

        Ok(())
    }
}
