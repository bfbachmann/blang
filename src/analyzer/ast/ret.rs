use std::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::lexer::pos::{Locatable, Position};
use crate::parser::ast::ret::Ret;
use crate::{format_code, locatable_impl, util};

/// Represents an analyzed return statement.
#[derive(Clone, Debug)]
pub struct ARet {
    pub val: Option<AExpr>,
    start_pos: Position,
    end_pos: Position,
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
        util::opts_eq(&self.val, &other.val)
    }
}

locatable_impl!(ARet);

impl ARet {
    pub fn from(ctx: &mut ProgramContext, ret: &Ret) -> Self {
        let start_pos = ret.start_pos().clone();
        let end_pos = ret.start_pos().clone();

        // Make sure we are inside a function body. If not, record the error and return a dummy
        // value.
        if !ctx.is_in_fn() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::UnexpectedReturn,
                "cannot return from outside function body",
                ret,
            ));

            return ARet {
                val: None,
                start_pos,
                end_pos,
            };
        }

        match &ret.value {
            Some(expr) => {
                // We're returning a value. Make sure the value is of the expected type.
                let a_expr = match ctx.get_cur_expected_ret_type_key() {
                    Some(expected_type_key) => AExpr::from(
                        ctx,
                        expr.clone(),
                        Some(expected_type_key),
                        false,
                        false,
                        false,
                    ),
                    None => {
                        ctx.insert_err(AnalyzeError::new(
                            ErrorKind::MismatchedTypes,
                            "cannot return value from function with no return type",
                            expr,
                        ));

                        AExpr::from(ctx, expr.clone(), None, false, false, false)
                    }
                };

                ARet {
                    val: Some(a_expr),
                    start_pos,
                    end_pos,
                }
            }
            None => {
                // This is an empty return. Make sure we're not expecting a return type.
                match ctx.get_cur_expected_ret_type_key() {
                    Some(expected) => {
                        ctx.insert_err(AnalyzeError::new(
                            ErrorKind::MismatchedTypes,
                            format_code!(
                                "expected return value of type {}, but found empty return",
                                ctx.display_type_for_key(expected),
                            )
                            .as_str(),
                            ret,
                        ));
                    }
                    None => {}
                };

                ARet {
                    val: None,
                    start_pos,
                    end_pos,
                }
            }
        }
    }
}
