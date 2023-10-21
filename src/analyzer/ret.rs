use std::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::ProgramContext;
use crate::lexer::pos::{Locatable, Position};
use crate::parser::ret::Ret;
use crate::{format_code, locatable_impl, util};

/// Represents an analyzed return statement.
#[derive(Clone, Debug)]
pub struct RichRet {
    pub val: Option<RichExpr>,
    start_pos: Position,
    end_pos: Position,
}

impl fmt::Display for RichRet {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(expr) = &self.val {
            write!(f, "return {}", expr)
        } else {
            write!(f, "return")
        }
    }
}

impl PartialEq for RichRet {
    fn eq(&self, other: &Self) -> bool {
        util::opts_eq(&self.val, &other.val)
    }
}

locatable_impl!(RichRet);

impl RichRet {
    pub fn from(ctx: &mut ProgramContext, ret: Ret) -> Self {
        let start_pos = ret.start_pos().clone();
        let end_pos = ret.start_pos().clone();

        // Make sure we are inside a function body. If not, record the error and return a dummy
        // value.
        if !ctx.is_in_fn() {
            ctx.add_err(AnalyzeError::new(
                ErrorKind::UnexpectedReturn,
                "cannot return from outside function body",
                &ret,
            ));

            return RichRet {
                val: None,
                start_pos,
                end_pos,
            };
        }

        match ret.value {
            Some(expr) => {
                // We're returning a value. Make sure the value is of the expected type.
                let rich_expr = RichExpr::from(ctx, expr.clone());
                match ctx.return_type() {
                    Some(expected_type_id) => {
                        // Skip the type check if either type is unknown. This will be the case if
                        // semantic analysis on either type already failed.
                        let expected_type = ctx.must_get_resolved_type(expected_type_id);
                        let expr_type = ctx.must_get_resolved_type(&rich_expr.type_id);
                        if !expected_type.is_unknown()
                            && !expr_type.is_unknown()
                            && expected_type != expr_type
                        {
                            ctx.add_err(AnalyzeError::new(
                                ErrorKind::MismatchedTypes,
                                format_code!(
                                    "cannot return value of type {} from function with return \
                                    type {}",
                                    expr_type,
                                    expected_type,
                                )
                                .as_str(),
                                &expr,
                            ));
                        }
                    }
                    None => {
                        ctx.add_err(AnalyzeError::new(
                            ErrorKind::MismatchedTypes,
                            "cannot return value from function with no return type",
                            &expr,
                        ));
                    }
                };

                RichRet {
                    val: Some(rich_expr),
                    start_pos,
                    end_pos,
                }
            }
            None => {
                // This is an empty return. Make sure we're not expecting a return type.
                match ctx.return_type() {
                    Some(expected) => {
                        ctx.add_err(AnalyzeError::new(
                            ErrorKind::MismatchedTypes,
                            format_code!(
                                "expected return value of type {}, but found empty return",
                                expected,
                            )
                            .as_str(),
                            &ret,
                        ));
                    }
                    None => {}
                };

                RichRet {
                    val: None,
                    start_pos,
                    end_pos,
                }
            }
        }
    }
}
