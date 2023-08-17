use core::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::ProgramContext;
use crate::format_code;
use crate::parser::var_assign::VariableAssignment;

/// Represents a semantically valid and type-rich variable assignment.
#[derive(Clone, PartialEq, Debug)]
pub struct RichVarAssign {
    pub name: String,
    pub val: RichExpr,
}

impl fmt::Display for RichVarAssign {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.name, self.val)
    }
}

impl RichVarAssign {
    /// Performs semantic analysis on the given variable assignment and returns a type-rich version
    /// of it.
    pub fn from(ctx: &mut ProgramContext, assign: VariableAssignment) -> Self {
        // Analyze the expression representing the value assigned to the variable.
        let rich_expr = RichExpr::from(ctx, assign.value.clone());

        // Make sure the variable has been defined.
        let var_type = ctx.get_var(assign.name.as_str());
        if let Some(typ) = var_type {
            // Make sure the variable type is the same as the expression type.
            if typ != &rich_expr.typ {
                ctx.add_err(AnalyzeError::new_with_locatable(
                    ErrorKind::IncompatibleTypes,
                    format_code!(
                        "cannot assign value of type {} to variable {}: {}",
                        &rich_expr.typ,
                        &assign.name,
                        &typ
                    )
                    .as_str(),
                    Box::new(assign.value.clone()),
                ));
            }
        } else {
            ctx.add_err(AnalyzeError::new_with_locatable(
                ErrorKind::VariableNotDefined,
                format!("cannot assign to undeclared variable {}", assign.name).as_str(),
                Box::new(assign.clone()),
            ));
        }

        RichVarAssign {
            name: assign.name,
            val: rich_expr,
        }
    }
}
