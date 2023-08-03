use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::RichType;
use crate::analyzer::AnalyzeResult;
use crate::parser::statement::Statement;
use crate::parser::var_dec::VariableDeclaration;

/// Represents a semantically valid and type-rich variable declaration.
#[derive(PartialEq, Debug, Clone)]
pub struct RichVarDecl {
    pub typ: RichType,
    pub name: String,
    pub val: RichExpr,
}

impl fmt::Display for RichVarDecl {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} = {}", self.typ, self.name, self.val)
    }
}

impl RichVarDecl {
    /// Performs semantic analysis on the given variable declaration and returns a type-rich version
    /// of it, or an error if the variable declaration is semantically invalid.
    pub fn from(ctx: &mut ProgramContext, var_decl: VariableDeclaration) -> AnalyzeResult<Self> {
        // Check if the variable is already defined in this scope.
        if ctx.get_var(var_decl.name.as_str()).is_some() {
            return Err(AnalyzeError::new_from_statement(
                ErrorKind::VariableAlreadyDefined,
                &Statement::VariableDeclaration(var_decl.clone()),
                format!(
                    "variable {} was already defined in this scope",
                    var_decl.name,
                )
                .as_str(),
            ));
        }

        // Analyze the variable type.
        let var_type = RichType::from(ctx, &var_decl.typ)?;

        // Check the expression being assigned to this new variable.
        let rich_expr = RichExpr::from(ctx, var_decl.value.clone())?;
        if rich_expr.typ != var_type {
            return Err(AnalyzeError::new_from_statement(
                ErrorKind::IncompatibleTypes,
                &Statement::VariableDeclaration(var_decl.clone()),
                format!(
                    "cannot assign value of type {} to variable {} of type {}",
                    &rich_expr.typ, &var_decl.name, &var_decl.typ
                )
                .as_str(),
            ));
        }

        // The variable expression is valid. Add it to the program context.
        ctx.add_var(var_decl.name.as_str(), rich_expr.typ.clone());
        Ok(RichVarDecl {
            typ: var_type,
            name: var_decl.name,
            val: rich_expr,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::analyzer::error::{AnalyzeError, ErrorKind};
    use crate::analyzer::expr::{RichExpr, RichExprKind};
    use crate::analyzer::prog_context::ProgramContext;
    use crate::analyzer::r#type::RichType;
    use crate::analyzer::var_dec::RichVarDecl;
    use crate::parser::expr::Expression;
    use crate::parser::r#type::Type;
    use crate::parser::var_dec::VariableDeclaration;

    #[test]
    fn var_already_defined() {
        let mut ctx = ProgramContext::new();
        let var_decl = VariableDeclaration::new(
            Type::String,
            "my_string".to_string(),
            Expression::StringLiteral("bingo".to_string()),
        );
        let result = RichVarDecl::from(&mut ctx, var_decl.clone());
        assert_eq!(
            result,
            Ok(RichVarDecl {
                typ: RichType::String,
                name: "my_string".to_string(),
                val: RichExpr {
                    kind: RichExprKind::StringLiteral("bingo".to_string()),
                    typ: RichType::String,
                }
            })
        );

        let result = RichVarDecl::from(&mut ctx, var_decl);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::VariableAlreadyDefined,
                ..
            })
        ));
    }

    #[test]
    fn type_mismatch() {
        let mut ctx = ProgramContext::new();
        let var_decl = VariableDeclaration::new(
            Type::I64,
            "my_string".to_string(),
            Expression::StringLiteral("bingo".to_string()),
        );
        let result = RichVarDecl::from(&mut ctx, var_decl);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::IncompatibleTypes,
                ..
            })
        ));
    }
}
