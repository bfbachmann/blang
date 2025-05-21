use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::error::{err_empty_return, err_unexpected_return, err_unexpected_return_val};
use crate::analyzer::prog_context::ProgramContext;
use crate::lexer::pos::{Locatable, Span};
use crate::locatable_impl;
use crate::parser::ast::ret::Ret;

/// Represents an analyzed return statement.
#[derive(Clone, Debug)]
pub struct ARet {
    pub val: Option<AExpr>,
    pub span: Span,
}

impl fmt::Display for ARet {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(expr) = &self.val {
            write!(f, "return {}", expr)
        } else {
            write!(f, "return")
        }
    }
}

impl PartialEq for ARet {
    fn eq(&self, other: &Self) -> bool {
        self.val == other.val
    }
}

locatable_impl!(ARet);

impl ARet {
    pub fn from(ctx: &mut ProgramContext, ret: &Ret) -> Self {
        let span = ret.span;

        // Make sure we are inside a function body. If not, record the error and return a dummy
        // value.
        if !ctx.is_in_fn() {
            ctx.insert_err(err_unexpected_return(ret.span));
            return ARet { val: None, span };
        }

        match &ret.value {
            Some(expr) => {
                // We're returning a value. Make sure the value is of the expected type.
                let a_expr = match ctx.cur_expected_ret_type_key() {
                    Some(expected_type_key) => {
                        AExpr::from(ctx, expr.clone(), Some(expected_type_key), false, false)
                    }
                    None => {
                        ctx.insert_err(err_unexpected_return_val(ret.span));
                        AExpr::from(ctx, expr.clone(), None, false, false)
                    }
                };

                ARet {
                    val: Some(a_expr),
                    span,
                }
            }
            None => {
                // This is an empty return. Make sure we're not expecting a return type.
                if let Some(expected_tk) = ctx.cur_expected_ret_type_key() {
                    let err = err_empty_return(ctx, expected_tk, ret.span);
                    ctx.insert_err(err);
                }

                ARet { val: None, span }
            }
        }
    }
}
