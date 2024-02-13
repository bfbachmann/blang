use core::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::format_code;
use crate::parser::ast::var_assign::VariableAssignment;

/// Represents a semantically valid and type-rich variable assignment.
#[derive(Clone, PartialEq, Debug)]
pub struct AVarAssign {
    pub target: AExpr,
    pub val: AExpr,
}

impl fmt::Display for AVarAssign {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.target, self.val)
    }
}

impl AVarAssign {
    /// Performs semantic analysis on the given variable assignment and returns a type-rich version
    /// of it.
    pub fn from(ctx: &mut ProgramContext, assign: &VariableAssignment) -> Self {
        // Analyze the expression representing the target value of the assignment.
        let target = AExpr::from(ctx, assign.target.clone(), None, false, false);

        // Make sure the variable being assigned to exists and is mutable.
        let symbol = match target.get_base_symbol() {
            Some(s) => s,
            None => {
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::InvalidAssignmentTarget,
                    format_code!("cannot assign to non-variable {}", target.display(ctx)).as_str(),
                    assign,
                ));

                return AVarAssign {
                    target,
                    val: AExpr::from(ctx, assign.value.clone(), None, false, false),
                };
            }
        };

        let var_name = symbol.name.clone();
        match ctx.get_symbol(var_name.as_str()) {
            Some(var) => {
                // The variable exists, so make sure it is mutable.
                if var.is_const {
                    ctx.insert_err(
                        AnalyzeError::new(
                            ErrorKind::ImmutableAssignment,
                            format_code!("cannot assign to constant {}", target.display(ctx))
                                .as_str(),
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
                            format_code!(
                                "cannot assign to immutable variable {}",
                                target.display(ctx)
                            )
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
                    target,
                    val: AExpr::from(ctx, assign.value.clone(), None, false, false),
                };
            }
        };

        // Analyze the expression representing the value assigned to the variable.
        let a_expr = AExpr::from(
            ctx,
            assign.value.clone(),
            Some(target.type_key),
            false,
            false,
        );

        AVarAssign {
            target,
            val: a_expr,
        }
    }
}
