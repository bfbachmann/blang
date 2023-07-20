use core::fmt;
use std::fmt::Formatter;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::AnalyzeResult;
use crate::parser::var_assign::VariableAssignment;

/// Represents a semantically valid and type-rich variable assignment.
#[derive(PartialEq, Debug)]
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
    /// of it, or an error if the statement is variable assignment invalid.
    pub fn from(ctx: &mut ProgramContext, assign: VariableAssignment) -> AnalyzeResult<Self> {
        // Analyze the expression representing the value assigned to the variable.
        let rich_expr = RichExpr::from(ctx, assign.value)?;

        // Make sure the variable has been defined.
        let decl = ctx.get_var(assign.name.as_str());
        if let None = decl {
            return Err(AnalyzeError::new(
                ErrorKind::VariableNotDefined,
                format!("cannot assign to undeclared variable {}", assign.name).as_str(),
            ));
        }

        // Make sure the variable type is the same as the expression type.
        let decl = decl.unwrap();
        if decl.typ != rich_expr.typ {
            return Err(AnalyzeError::new(
                ErrorKind::IncompatibleTypes,
                format!(
                    "cannot assign value of type {} to variable {} of type {}",
                    &rich_expr.typ, &assign.name, &decl.typ
                )
                .as_str(),
            ));
        }

        Ok(RichVarAssign {
            name: assign.name,
            val: rich_expr,
        })
    }
}
