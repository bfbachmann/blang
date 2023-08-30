use std::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::format_code;
use crate::parser::statement::Statement;
use crate::parser::var_dec::VariableDeclaration;

/// Represents a semantically valid and type-rich variable declaration.
#[derive(PartialEq, Debug, Clone)]
pub struct RichVarDecl {
    pub typ: TypeId,
    pub name: String,
    pub val: RichExpr,
}

impl fmt::Display for RichVarDecl {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {} = {}", self.name, self.typ, self.val)
    }
}

impl RichVarDecl {
    /// Performs semantic analysis on the given variable declaration and returns a type-rich version
    /// of it.
    pub fn from(ctx: &mut ProgramContext, var_decl: VariableDeclaration) -> Self {
        // Check if the variable is already defined in this scope.
        if ctx.get_var(var_decl.name.as_str()).is_some() {
            ctx.add_err(AnalyzeError::new_from_statement(
                ErrorKind::VariableAlreadyDefined,
                &Statement::VariableDeclaration(var_decl.clone()),
                format_code!(
                    "variable {} was already defined in this scope",
                    var_decl.name,
                )
                .as_str(),
            ));
        }

        // Check the expression being assigned to this new variable.
        let rich_expr = RichExpr::from(ctx, var_decl.value.clone());

        // Analyze the variable type. It might be empty because type annotations are optional
        // in variable declarations. If the type is not specified, it will be inferred from the
        // assigned expression.
        let var_type = match &var_decl.typ {
            // If the variable was declared with a type, analyze it and make sure it matches the
            // expression type.
            Some(typ) => {
                let declared_type = RichType::analyze(ctx, &typ);
                if &rich_expr.type_id != &declared_type {
                    ctx.add_err(AnalyzeError::new_from_statement(
                        ErrorKind::IncompatibleTypes,
                        &Statement::VariableDeclaration(var_decl.clone()),
                        format_code!(
                            "cannot assign value of type {} to variable {}",
                            &rich_expr.type_id,
                            format!("{}: {}", &var_decl.name, &declared_type),
                        )
                        .as_str(),
                    ));
                }

                declared_type
            }
            // Otherwise, use the expression type.
            None => rich_expr.type_id.clone(),
        };

        // The variable expression is valid. Add it to the program context.
        ctx.add_var(var_decl.name.as_str(), rich_expr.type_id.clone());
        RichVarDecl {
            typ: var_type,
            name: var_decl.name,
            val: rich_expr,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::analyzer::error::{AnalyzeError, ErrorKind};
    use crate::analyzer::expr::{RichExpr, RichExprKind};
    use crate::analyzer::prog_context::ProgramContext;
    use crate::analyzer::r#type::TypeId;
    use crate::analyzer::var_dec::RichVarDecl;
    use crate::lexer::pos::Position;
    use crate::parser::expr::Expression;
    use crate::parser::r#type::Type;
    use crate::parser::string_lit::StringLit;
    use crate::parser::var_dec::VariableDeclaration;

    #[test]
    fn var_already_defined() {
        let mut ctx = ProgramContext::new();
        let var_decl = VariableDeclaration::new(
            Some(Type::string()),
            "my_string".to_string(),
            Expression::StringLiteral(StringLit::new_with_default_pos("bingo")),
            Position::default(),
            Position::default(),
        );
        let result = RichVarDecl::from(&mut ctx, var_decl.clone());
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            RichVarDecl {
                typ: TypeId::string(),
                name: "my_string".to_string(),
                val: RichExpr {
                    kind: RichExprKind::StringLiteral("bingo".to_string()),
                    type_id: TypeId::string(),
                }
            }
        );

        RichVarDecl::from(&mut ctx, var_decl);
        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::VariableAlreadyDefined,
                ..
            }
        ));
    }

    #[test]
    fn type_mismatch() {
        let mut ctx = ProgramContext::new();
        let var_decl = VariableDeclaration::new(
            Some(Type::i64()),
            "my_string".to_string(),
            Expression::StringLiteral(StringLit::new_with_default_pos("bingo")),
            Position::default(),
            Default::default(),
        );
        RichVarDecl::from(&mut ctx, var_decl);
        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::IncompatibleTypes,
                ..
            }
        ));
    }
}
