use core::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::symbol::ASymbol;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::format_code;
use crate::parser::var_assign::VariableAssignment;

/// Represents a semantically valid and type-rich variable assignment.
#[derive(Clone, PartialEq, Debug)]
pub struct AVarAssign {
    pub symbol: ASymbol,
    pub val: AExpr,
}

impl fmt::Display for AVarAssign {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.symbol, self.val)
    }
}

impl AVarAssign {
    /// Performs semantic analysis on the given variable assignment and returns a type-rich version
    /// of it.
    pub fn from(ctx: &mut ProgramContext, assign: &VariableAssignment) -> Self {
        // Make sure the variable being assigned to exists and is mutable.
        let symbol = ASymbol::from(ctx, &assign.symbol, false, None);
        let var_name = assign.symbol.name.clone();
        match ctx.get_symbol(var_name.as_str()) {
            Some(var) => {
                // The variable exists, so make sure it is mutable.
                if var.is_const {
                    ctx.insert_err(
                        AnalyzeError::new(
                            ErrorKind::ImmutableAssignment,
                            format_code!("cannot assign to constant {}", assign.symbol).as_str(),
                            assign,
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
                    ctx.insert_err(
                        AnalyzeError::new(
                            ErrorKind::ImmutableAssignment,
                            format_code!("cannot assign to immutable variable {}", assign.symbol)
                                .as_str(),
                            assign,
                        )
                        .with_help(
                            format_code!("Consider declaring {} as mutable.", var_name).as_str(),
                        ),
                    )
                }
            }
            None => {
                // The variable does not exist. Record the error and skip any further checks.
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::UndefSymbol,
                    format_code!("cannot assign to undefined variable {}", var_name).as_str(),
                    assign,
                ));

                return AVarAssign {
                    symbol,
                    val: AExpr::from(ctx, assign.value.clone(), None, false),
                };
            }
        };

        // Analyze the expression representing the value assigned to the variable.
        let symbol_tk = symbol.get_type_key();
        let a_expr = AExpr::from(ctx, assign.value.clone(), Some(symbol_tk), false);

        AVarAssign {
            symbol,
            val: a_expr,
        }
    }
}
