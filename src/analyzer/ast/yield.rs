use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::lexer::pos::Span;
use crate::locatable_impl;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::r#yield::Yield;
use crate::Locatable;

/// Represents an analyzed yield statement.
#[derive(Clone, Debug)]
pub struct AYield {
    pub value: AExpr,
    pub span: Span,
}

impl fmt::Display for AYield {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "yield {}", self.value)
    }
}

impl PartialEq for AYield {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

locatable_impl!(AYield);

impl AYield {
    /// Performs semantic analysis on a `yield` statement.
    pub fn from(ctx: &mut ProgramContext, yld: &Yield) -> AYield {
        let span = yld.span().clone();

        // Make sure we are inside a `from` block. If not, record the error and
        // return a dummy value.
        if !ctx.is_in_from_block() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::UnexpectedYield,
                format_code!("cannot {} from outside {} block", "yield", "from").as_str(),
                yld,
            ));

            return AYield {
                value: AExpr::new_zero_value(ctx, Type::new_unresolved("<unknown>")),
                span,
            };
        }

        // We're yielding a value. Make sure the value is of the expected type.
        let a_expr = match ctx.get_cur_expected_yield_type_key() {
            Some(expected_type_key) => AExpr::from(
                ctx,
                yld.value.clone(),
                Some(expected_type_key),
                false,
                false,
            ),

            None => {
                // In this case, no expected yield type was specified,
                // so we'll set one based on the type of this yield on
                // the assumption that it's the first yield in the current
                // `from` block, and all other yields should be of the same
                // type.
                let a_expr = AExpr::from(ctx, yld.value.clone(), None, false, false);
                if a_expr.type_key != ctx.unknown_type_key() {
                    ctx.set_cur_expected_yield_type_key(a_expr.type_key);
                }

                a_expr
            }
        };

        AYield {
            value: a_expr,
            span,
        }
    }
}
