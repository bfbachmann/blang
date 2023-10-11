use std::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::{ProgramContext, ScopedSymbol};
use crate::analyzer::r#type::{RichType, TypeId};
use crate::format_code;
use crate::parser::var_dec::VariableDeclaration;

/// Represents a semantically valid and type-rich variable declaration.
#[derive(PartialEq, Debug, Clone)]
pub struct RichVarDecl {
    pub type_id: TypeId,
    pub name: String,
    pub val: RichExpr,
}

impl fmt::Display for RichVarDecl {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {} = {}", self.name, self.type_id, self.val)
    }
}

impl RichVarDecl {
    /// Performs semantic analysis on the given variable declaration and returns a type-rich version
    /// of it.
    pub fn from(ctx: &mut ProgramContext, var_decl: VariableDeclaration) -> Self {
        // Check the expression being assigned to this new variable. Note that it's okay for
        // the variable name to collide with that of another variable. In this case, the old
        // variable will simply be replaced with this one in the current scope.
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
                    ctx.add_err(AnalyzeError::new(
                        ErrorKind::MismatchedTypes,
                        format_code!(
                            "cannot assign value of type {} to variable {}",
                            &rich_expr.type_id,
                            format!("{}: {}", &var_decl.name, &declared_type),
                        )
                        .as_str(),
                        &var_decl,
                    ));
                }

                declared_type
            }
            // Otherwise, use the expression type.
            None => rich_expr.type_id.clone(),
        };

        // The variable expression is valid. Add it to the program context.
        ctx.add_symbol(ScopedSymbol::new(
            var_decl.name.as_str(),
            rich_expr.type_id.clone(),
            var_decl.is_mut,
            false,
        ));

        RichVarDecl {
            type_id: var_type,
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
    use crate::parser::bool_lit::BoolLit;
    use crate::parser::expr::Expression;
    use crate::parser::r#type::Type;
    use crate::parser::str_lit::StrLit;
    use crate::parser::var_dec::VariableDeclaration;

    #[test]
    fn var_redeclared() {
        let mut ctx = ProgramContext::new();
        let var_decl = VariableDeclaration::new(
            Some(Type::str()),
            false,
            "my_var".to_string(),
            Expression::StrLiteral(StrLit::new_with_default_pos("bingo")),
            Position::default(),
            Position::default(),
        );
        let result = RichVarDecl::from(&mut ctx, var_decl.clone());
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            RichVarDecl {
                type_id: TypeId::str(),
                name: "my_var".to_string(),
                val: RichExpr::new(RichExprKind::StrLiteral("bingo".to_string()), TypeId::str())
            }
        );
        assert_eq!(ctx.get_symbol("my_var").unwrap().type_id, TypeId::str());

        let new_var_decl = VariableDeclaration::new(
            Some(Type::bool()),
            false,
            "my_var".to_string(),
            Expression::BoolLiteral(BoolLit::new_with_default_pos(true)),
            Position::default(),
            Position::default(),
        );

        let result = RichVarDecl::from(&mut ctx, new_var_decl);
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            RichVarDecl {
                type_id: TypeId::bool(),
                name: "my_var".to_string(),
                val: RichExpr::new(RichExprKind::BoolLiteral(true), TypeId::bool())
            }
        );
        assert_eq!(ctx.get_symbol("my_var").unwrap().type_id, TypeId::bool());
    }

    #[test]
    fn type_mismatch() {
        let mut ctx = ProgramContext::new();
        let var_decl = VariableDeclaration::new(
            Some(Type::i64()),
            false,
            "my_string".to_string(),
            Expression::StrLiteral(StrLit::new_with_default_pos("bingo")),
            Position::default(),
            Default::default(),
        );
        RichVarDecl::from(&mut ctx, var_decl);
        assert!(matches!(
            ctx.errors().remove(0),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));
    }
}
