use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::fmt::format_code_vec;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::func_call::FuncCall;

/// Function call (can be either direct or indirect).
#[derive(Clone, Debug, PartialEq)]
pub struct AFnCall {
    pub fn_expr: AExpr,
    pub args: Vec<AExpr>,
    pub maybe_ret_type_key: Option<TypeKey>,
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
    pub fn from(ctx: &mut ProgramContext, call: &FuncCall) -> AFnCall {
        // Analyze the expression that should represent a function.
        let fn_expr = AExpr::from_with_pref(ctx, call.fn_expr.clone(), None, false, false, true);

        // This value will serve as a placeholder for cases where analysis fails on the function
        // call, and we need to abort early.
        let placeholder = AFnCall {
            fn_expr: AExpr::new_with_default_pos(AExprKind::Unknown, ctx.unknown_type_key()),
            args: vec![],
            maybe_ret_type_key: Some(ctx.unknown_type_key()),
        };

        // Return a placeholder value if the expression already failed analysis or has the wrong
        // type.
        let fn_type = match ctx.must_get_type(fn_expr.type_key) {
            AType::Function(fn_sig) => fn_sig,

            // If the function expression has an unknown type, it means expression analysis already
            // failed, so we should not proceed.
            AType::Unknown(_) => {
                return placeholder;
            }

            _ => {
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::MismatchedTypes,
                    format_code!(
                        "type {} is not callable",
                        ctx.display_type(fn_expr.type_key)
                    )
                    .as_str(),
                    &call.fn_expr,
                ));
                return placeholder;
            }
        };

        // Check if `self` is being passed implicitly (i.e. check if the call takes the form
        // `<expr>.this_method(...)`).
        let maybe_self = match &fn_type.maybe_impl_type_key {
            Some(_) => match &fn_expr.kind {
                AExprKind::MemberAccess(access) => match &access.base_expr.kind {
                    AExprKind::Symbol(symbol) if symbol.is_type => None,
                    _ => Some(&access.base_expr),
                },
                _ => None,
            },
            None => None,
        };

        // Make sure the call has the right number of arguments (making sure to add 1 to the actual
        // argument count if there is an implicit `self` argument).
        let expected_args = fn_type.args.len();
        let actual_args = match &maybe_self {
            Some(_) => call.args.len() + 1,
            None => call.args.len(),
        };

        if actual_args != expected_args {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::WrongNumberOfArgs,
                format!(
                    "{} expects {} {}, but found {}",
                    format_code!("{}", fn_type.display(ctx)),
                    expected_args,
                    match expected_args {
                        1 => "argument",
                        _ => "arguments",
                    },
                    actual_args
                )
                .as_str(),
                call,
            ));
            return AFnCall {
                fn_expr,
                args: vec![],
                maybe_ret_type_key: Some(ctx.unknown_type_key()),
            };
        }

        // Analyze each argument expression.
        let maybe_ret_type_key = fn_type.maybe_ret_type_key;
        let fn_type_args = fn_type.args.clone();
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
        for (expected_arg, actual_arg) in fn_type_args_iter.zip(call.args.iter()) {
            // The way we analyze the argument depends on whether its expected type
            // is generic.
            let expected_arg_type = ctx.must_get_type(expected_arg.type_key);
            let analyzed_arg = if expected_arg_type.is_generic() {
                analyze_generic_arg(ctx, expected_arg.type_key, actual_arg)
            } else {
                AExpr::from(
                    ctx,
                    actual_arg.clone(),
                    Some(expected_arg.type_key),
                    false,
                    false,
                )
            };

            args.push(analyzed_arg);
        }

        AFnCall {
            fn_expr,
            args,
            maybe_ret_type_key,
        }
    }

    /// Returns this function call in human-readable form.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let s = format!("{}(", self.fn_expr.display(ctx));

        for (i, arg) in self.args.iter().enumerate() {
            match i {
                0 => format!("{}", arg.display(ctx)),
                _ => format!(", {}", arg.display(ctx)),
            };
        }

        s + ")"
    }
}

/// Analyzes an argument whose expected type is some generic type and returns it.
/// This also involves checking that the argument type satisfies spec requirements
/// laid out by the generic parameter.
fn analyze_generic_arg(
    ctx: &mut ProgramContext,
    expected_arg_type_key: TypeKey,
    actual_arg: &Expression,
) -> AExpr {
    // Analyze the argument without any expected type.
    let analyzed_arg = AExpr::from(ctx, actual_arg.clone(), None, false, false);

    // Skip further checks if the arg already failed analysis.
    if ctx.must_get_type(analyzed_arg.type_key).is_unknown() {
        return analyzed_arg;
    }

    // Find the type keys for all specs that are not implemented by this arg.
    let missing_spec_type_keys =
        ctx.get_missing_spec_impls(analyzed_arg.type_key, expected_arg_type_key);
    if !missing_spec_type_keys.is_empty() {
        let type_string = ctx.display_type(analyzed_arg.type_key);
        let missing_specs_string = format_code_vec(
            &missing_spec_type_keys
                .iter()
                .map(|k| ctx.display_type(*k))
                .collect::<Vec<String>>(),
            ", ",
        );
        let generic_type_string = ctx.display_type(expected_arg_type_key);

        ctx.insert_err(
            AnalyzeError::new(
                ErrorKind::SpecNotSatisfied,
                format_code!(
                    "argument type {} doesn't satisfy constraints for parameter {}",
                    type_string,
                    generic_type_string,
                )
                .as_str(),
                actual_arg,
            )
            .with_detail(
                format!(
                    "Type {} is missing implementations for specs: {}.",
                    format_code!(type_string),
                    missing_specs_string
                )
                .as_str(),
            ),
        );
    }

    analyzed_arg
}
