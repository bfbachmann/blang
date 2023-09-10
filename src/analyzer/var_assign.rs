use core::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::var::RichVar;
use crate::format_code;
use crate::parser::var_assign::VariableAssignment;

/// Represents a semantically valid and type-rich variable assignment.
#[derive(Clone, PartialEq, Debug)]
pub struct RichVarAssign {
    pub var: RichVar,
    pub val: RichExpr,
}

impl fmt::Display for RichVarAssign {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.var, self.val)
    }
}

impl RichVarAssign {
    /// Performs semantic analysis on the given variable assignment and returns a type-rich version
    /// of it.
    pub fn from(ctx: &mut ProgramContext, assign: VariableAssignment) -> Self {
        // Analyze the expression representing the value assigned to the variable.
        let rich_expr = RichExpr::from(ctx, assign.value.clone());

        // Make sure the variable has been defined. If not, we'll record the error and skip type
        // match checks.
        let rich_var = RichVar::from(ctx, &assign.var, false);
        let referenced_type = ctx.get_resolved_type(rich_var.get_type_id());
        match referenced_type {
            Some(typ) => {
                // Make sure the variable type is the same as the expression type.
                let expr_type = ctx.get_resolved_type(&rich_expr.type_id).unwrap();
                if !typ.same_as(expr_type) {
                    ctx.add_err(AnalyzeError::new_with_locatable(
                        ErrorKind::IncompatibleTypes,
                        format_code!(
                            "cannot assign value of type {} to variable {}",
                            &expr_type,
                            format!("{}: {}", &assign.var, &typ),
                        )
                        .as_str(),
                        Box::new(assign.value.clone()),
                    ));
                }
            }
            None => {
                // The variable reference being assigned to is invalid, so we'll skip any further
                // analysis on this statement.
            }
        }

        // Make sure the variable being assigned to is mutable.
        let var_name = assign.var.var_name.clone();
        let var = ctx.get_var(var_name.as_str()).unwrap();
        if !var.is_mut {
            let help = if var.is_arg {
                // TODO: Update this when reference types are implemented.
                format_code!(
                    "consider assigning {} to a mutable local variable",
                    var_name
                )
            } else {
                format_code!("consider declaring {} as mutable", var_name)
            };

            ctx.add_err(
                AnalyzeError::new_with_locatable(
                    ErrorKind::ImmutableAssignment,
                    format_code!("cannot assign to immutable variable {}", assign.var).as_str(),
                    Box::new(assign),
                )
                .with_help(help.as_str()),
            )
        }

        RichVarAssign {
            var: rich_var,
            val: rich_expr,
        }
    }
}
