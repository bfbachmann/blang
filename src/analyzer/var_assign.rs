use core::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::symbol::RichSymbol;
use crate::format_code;
use crate::parser::var_assign::VariableAssignment;

/// Represents a semantically valid and type-rich variable assignment.
#[derive(Clone, PartialEq, Debug)]
pub struct RichVarAssign {
    pub symbol: RichSymbol,
    pub val: RichExpr,
}

impl fmt::Display for RichVarAssign {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.symbol, self.val)
    }
}

impl RichVarAssign {
    /// Performs semantic analysis on the given variable assignment and returns a type-rich version
    /// of it.
    pub fn from(ctx: &mut ProgramContext, assign: VariableAssignment) -> Self {
        // Make sure the variable being assigned to exists and is mutable.
        let symbol = RichSymbol::from(ctx, &assign.symbol, false, None);
        let var_name = assign.symbol.name.clone();
        match ctx.get_symbol(var_name.as_str()) {
            Some(var) => {
                // The variable exists, so make sure it is mutable.
                if var.is_const {
                    ctx.add_err(
                        AnalyzeError::new(
                            ErrorKind::ImmutableAssignment,
                            format_code!("cannot assign to constant {}", assign.symbol).as_str(),
                            &assign,
                        )
                        .with_help(
                            format_code!(
                                "Consider declaring {} as a mutable local variable.",
                                var_name
                            )
                            .as_str(),
                        ),
                    )
                } else if !var.is_mut {
                    ctx.add_err(
                        AnalyzeError::new(
                            ErrorKind::ImmutableAssignment,
                            format_code!("cannot assign to immutable variable {}", assign.symbol)
                                .as_str(),
                            &assign,
                        )
                        .with_help(
                            format_code!("Consider declaring {} as mutable.", var_name).as_str(),
                        ),
                    )
                }
            }
            None => {
                // The variable does not exist. Record the error and skip any further checks.
                ctx.add_err(AnalyzeError::new(
                    ErrorKind::UndefSymbol,
                    format_code!("cannot assign to undefined variable {}", var_name).as_str(),
                    &assign,
                ));

                return RichVarAssign {
                    symbol,
                    val: RichExpr::from(ctx, assign.value.clone(), None, false),
                };
            }
        };

        // Analyze the expression representing the value assigned to the variable.
        let symbol_tid = symbol.get_type_id();
        let rich_expr = RichExpr::from(ctx, assign.value.clone(), Some(symbol_tid), false);

        RichVarAssign {
            symbol,
            val: rich_expr,
        }
    }
}
