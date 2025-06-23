use std::collections::HashMap;
use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::func::AFnSig;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::symbol::{ASymbol, SymbolKind};
use crate::analyzer::check_types;
use crate::analyzer::error::{
    err_not_callable, err_type_annotations_needed, err_wrong_num_args, AnalyzeError,
};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::Span;
use crate::parser::ast::func_call::FnCall;
use crate::Locatable;

/// Function call (can be either direct or indirect).
#[derive(Clone, Debug, PartialEq)]
pub struct AFnCall {
    pub fn_expr: AExpr,
    pub args: Vec<AExpr>,
    pub maybe_ret_type_key: Option<TypeKey>,
    pub span: Span,
}

impl Display for AFnCall {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}(", self.fn_expr)?;

        for (i, arg) in self.args.iter().enumerate() {
            match i {
                0 => write!(f, "{}", arg)?,
                _ => write!(f, ", {}", arg)?,
            };
        }

        write!(f, ")")
    }
}

impl AFnCall {
    /// Performs semantic analysis on a function call and returns the analyzed version of it.
    pub fn from(
        ctx: &mut ProgramContext,
        call: &FnCall,
        maybe_expected_ret_tk: Option<TypeKey>,
    ) -> AFnCall {
        // Analyze the expression that should represent a function.
        let mut fn_expr =
            AExpr::from_with_pref(ctx, call.fn_expr.clone(), None, false, true, false, true);

        // This value will serve as a placeholder for cases where analysis fails on the function
        // call, and we need to abort early.
        let placeholder = AFnCall {
            fn_expr: AExpr::new_with_default_span(AExprKind::Unknown, ctx.unknown_type_key()),
            args: vec![],
            maybe_ret_type_key: Some(ctx.unknown_type_key()),
            span: call.span,
        };
        let type_annotations_needed_err =
            err_type_annotations_needed(ctx, fn_expr.type_key, *call.fn_expr.span());

        // Return a placeholder value if the expression already failed analysis or has the wrong
        // type.
        let fn_sig = match ctx.get_type(fn_expr.type_key) {
            AType::Function(fn_sig) => *fn_sig.clone(),

            // If the function expression has an unknown type, it means expression analysis already
            // failed, so we should not proceed.
            AType::Unknown(_) => {
                return placeholder;
            }

            _ => {
                let err = err_not_callable(ctx, fn_expr.type_key, *call.fn_expr.span());
                ctx.insert_err(err);
                return placeholder;
            }
        };

        // Check if `self` is being passed implicitly (i.e. check if the call takes the form
        // `<expr>.this_method(...)`).
        let maybe_self = match &fn_sig.maybe_impl_type_key {
            Some(_) => match &fn_expr.kind {
                AExprKind::MemberAccess(access) => match &access.base_expr.kind {
                    AExprKind::Symbol(symbol) if symbol.kind == SymbolKind::Type => None,
                    _ => Some(&access.base_expr),
                },
                _ => None,
            },
            None => None,
        };

        // Make sure the call has the right number of arguments (making sure to add 1 to the actual
        // argument count if there is an implicit `self` argument).
        let expected_args = fn_sig.args.len();
        let actual_args = match &maybe_self {
            Some(_) => call.args.len() + 1,
            None => call.args.len(),
        };

        if actual_args != expected_args {
            let err = err_wrong_num_args(ctx, expected_args, actual_args, &fn_sig, call.span);
            ctx.insert_err(err);

            return AFnCall {
                fn_expr,
                args: vec![],
                maybe_ret_type_key: Some(ctx.unknown_type_key()),
                span: call.span,
            };
        }

        // Include the `self` argument, if necessary.
        let mut maybe_ret_type_key = fn_sig.maybe_ret_type_key;
        let fn_type_args = fn_sig.args.clone();
        let mut fn_type_args_iter = fn_type_args.iter();
        let mut args: Vec<AExpr> = match maybe_self {
            Some(self_arg) => {
                // Advance the iterator through the arguments on the function type to skip the implicit
                // `self` arg.
                fn_type_args_iter.next();
                vec![self_arg.clone()]
            }
            None => vec![],
        };

        // Analyze call arguments.
        if fn_sig.is_parameterized() {
            let (symbol_tk, symbol_param_tks) = match &mut fn_expr.kind {
                AExprKind::Symbol(ASymbol {
                    type_key,
                    maybe_param_tks,
                    ..
                }) => (type_key, Some(maybe_param_tks)),

                AExprKind::MemberAccess(access) => (&mut access.member_type_key, None),

                // Just give up if the function expression is not a simple symbol or member access.
                _ => {
                    ctx.insert_err(type_annotations_needed_err);
                    return AFnCall {
                        fn_expr,
                        args: vec![],
                        maybe_ret_type_key: Some(ctx.unknown_type_key()),
                        span: call.span,
                    };
                }
            };

            // Analyze the arguments and try to figure out how generic types are mapped based on
            // argument types.
            let (analyzed_args, type_mappings, errs) =
                analyze_generic_args(ctx, &fn_sig, call, maybe_expected_ret_tk);
            args.extend(analyzed_args);

            let has_errs = !errs.is_empty();
            for err in errs {
                ctx.insert_err(err);
            }

            // Use resolved type mappings from arguments to monomorphize the function type.
            let params = &fn_sig.params.unwrap().params;
            let mut param_replacement_tks = vec![];
            let mut dummy_param_locs = vec![];
            let dummy_span = call.fn_expr.span();
            for param in params {
                let replacement_tk = *type_mappings.get(&param.generic_type_key).unwrap();
                if replacement_tk == ctx.unknown_type_key() {
                    // We failed to resolve at least one generic param, so don't attempt
                    // monomorphization on the function being called.
                    if !has_errs {
                        ctx.insert_err(type_annotations_needed_err);
                    }
                    return AFnCall {
                        fn_expr,
                        args,
                        maybe_ret_type_key,
                        span: call.span,
                    };
                }

                dummy_param_locs.push(dummy_span);
                param_replacement_tks.push(replacement_tk);
            }

            // Try to execute the monomorphization using the discovered params and update the
            // expression and symbol info using the result.
            fn_expr.type_key = ctx.try_execute_monomorphization(
                fn_expr.type_key,
                param_replacement_tks.clone(),
                &dummy_param_locs,
                &call.fn_expr,
            );

            *symbol_tk = fn_expr.type_key;
            if let Some(symbol_param_tks) = symbol_param_tks {
                *symbol_param_tks = Some(param_replacement_tks);
            }

            maybe_ret_type_key = ctx
                .get_type(fn_expr.type_key)
                .to_fn_sig()
                .maybe_ret_type_key;
        } else {
            // The function is monomorphic, so we can analyze and type-check arguments the normal
            // way.
            for (expected_arg, actual_arg) in fn_type_args_iter.zip(call.args.iter()) {
                let analyzed_arg = AExpr::from(
                    ctx,
                    actual_arg.clone(),
                    Some(expected_arg.type_key),
                    false,
                    false,
                );

                args.push(analyzed_arg);
            }
        }

        AFnCall {
            fn_expr,
            args,
            maybe_ret_type_key,
            span: call.span,
        }
    }

    /// Returns this function call in human-readable form.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let s = format!("{}(", self.fn_expr.display(ctx));

        for (i, arg) in self.args.iter().enumerate() {
            match i {
                0 => arg.display(ctx).to_string(),
                _ => format!(", {}", arg.display(ctx)),
            };
        }

        s + ")"
    }
}

/// This function takes a generic function and a set of arguments it's called with and
/// 1. analyzes the arguments
/// 2. tries to figure out if the arguments are valid
/// 3. tries to resolve the implied generic parameter type mappings given the argument types and
///    expected return type.
///
/// In other words, this function does generic type inference for calls to parameterized functions.
fn analyze_generic_args(
    ctx: &mut ProgramContext,
    fn_sig: &AFnSig,
    call: &FnCall,
    maybe_expected_ret_tk: Option<TypeKey>,
) -> (Vec<AExpr>, HashMap<TypeKey, TypeKey>, Vec<AnalyzeError>) {
    let unknown_tk = ctx.unknown_type_key();

    let mut errs = vec![];
    let mut args = Vec::with_capacity(call.args.len());
    let mut type_mappings: HashMap<TypeKey, TypeKey> = fn_sig
        .params
        .as_ref()
        .unwrap()
        .params
        .iter()
        .map(|param| (param.generic_type_key, unknown_tk))
        .collect();

    // If possible, try to determine type mappings based on expected return types.
    if let (Some(defined_ret_tk), Some(expected_ret_tk)) =
        (&fn_sig.maybe_ret_type_key, maybe_expected_ret_tk)
    {
        // We can ignore the error return value here because the caller is going to check
        // the return type anyway.
        let _ = check_types(
            ctx,
            *defined_ret_tk,
            expected_ret_tk,
            &mut type_mappings,
            &Span::default(),
        );
    }

    // Shift over defined args until they line up with the passed args. This is just to account for
    // the `self` arg.
    let mut defined_args_iter = fn_sig.args.iter();
    while defined_args_iter.len() > call.args.len() {
        defined_args_iter.next();
    }

    for (defined_arg, passed_arg) in defined_args_iter.zip(call.args.iter()) {
        // Analyze the passed argument.
        let mut a_passed_arg = AExpr::from(ctx, passed_arg.clone(), None, false, false);

        // Try to coerce the argument to the right type if necessary.
        if a_passed_arg.type_key != defined_arg.type_key {
            a_passed_arg = a_passed_arg.try_coerce_to(ctx, defined_arg.type_key);
        }

        let passed_arg_tk = a_passed_arg.type_key;
        args.push(a_passed_arg);

        // Check that the argument type matches the expected type, updating parameter type mappings
        // if necessary.
        if let Err(err) = check_types(
            ctx,
            defined_arg.type_key,
            passed_arg_tk,
            &mut type_mappings,
            passed_arg,
        ) {
            errs.push(err);
        }
    }

    (args, type_mappings, errs)
}
