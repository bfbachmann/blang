use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::ScopedSymbol;
use crate::analyzer::type_store::TypeKey;
use crate::parser::ast::var_dec::VariableDeclaration;

/// Represents a semantically valid and type-rich variable declaration.
#[derive(PartialEq, Debug, Clone)]
pub struct AVarDecl {
    pub type_key: TypeKey,
    pub name: String,
    pub val: AExpr,
}

impl fmt::Display for AVarDecl {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {} = {}", self.name, self.type_key, self.val)
    }
}

impl AVarDecl {
    /// Performs semantic analysis on the given variable declaration and returns a type-rich version
    /// of it.
    pub fn from(ctx: &mut ProgramContext, var_decl: &VariableDeclaration) -> Self {
        // Analyze the variable type. It might be empty because type annotations are optional
        // in variable declarations.
        let maybe_declared_tk = match &var_decl.maybe_type {
            Some(typ) => Some(ctx.resolve_type(typ)),
            None => None,
        };

        // Check the expression being assigned to this new variable. Note that it's okay for
        // the variable name to collide with that of another variable. In this case, the old
        // variable will simply be replaced with this one in the current scope.
        let rich_expr = AExpr::from(ctx, var_decl.value.clone(), maybe_declared_tk, false, false);

        // If the type is not specified, it will be inferred from the assigned expression.
        let type_key = match maybe_declared_tk {
            Some(tk) => tk,
            None => rich_expr.type_key,
        };

        // The variable expression is valid. Add it to the program context.
        ctx.insert_scoped_symbol(ScopedSymbol::new(
            var_decl.name.as_str(),
            rich_expr.type_key,
            var_decl.is_mut,
        ));

        AVarDecl {
            type_key,
            name: var_decl.name.clone(),
            val: rich_expr,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::analyzer::ast::expr::{AExpr, AExprKind};
    use crate::analyzer::ast::var_dec::AVarDecl;
    use crate::analyzer::error::{AnalyzeError, ErrorKind};
    use crate::analyzer::prog_context::ProgramContext;
    use crate::parser::ast::bool_lit::BoolLit;
    use crate::parser::ast::expr::Expression;
    use crate::parser::ast::r#type::Type;
    use crate::parser::ast::str_lit::StrLit;
    use crate::parser::ast::var_dec::VariableDeclaration;

    #[test]
    fn var_redeclared() {
        let mut ctx = ProgramContext::new_with_host_target("test", vec!["test"]);
        let var_decl = VariableDeclaration::new(
            Some(Type::new_unresolved("str")),
            false,
            "my_var".to_string(),
            Expression::StrLiteral(StrLit::new_with_default_pos("bingo")),
            Default::default(),
        );
        let result = AVarDecl::from(&mut ctx, &var_decl);
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            AVarDecl {
                type_key: ctx.str_type_key(),
                name: "my_var".to_string(),
                val: AExpr::new_with_default_pos(
                    AExprKind::StrLiteral("bingo".to_string()),
                    ctx.str_type_key()
                )
            }
        );
        assert_eq!(
            ctx.get_scoped_symbol(None, "my_var").unwrap().type_key,
            ctx.str_type_key()
        );

        let new_var_decl = VariableDeclaration::new(
            Some(Type::new_unresolved("bool")),
            false,
            "my_var".to_string(),
            Expression::BoolLiteral(BoolLit::new_with_default_pos(true)),
            Default::default(),
        );

        let result = AVarDecl::from(&mut ctx, &new_var_decl);
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            AVarDecl {
                type_key: ctx.bool_type_key(),
                name: "my_var".to_string(),
                val: AExpr::new_with_default_pos(AExprKind::BoolLiteral(true), ctx.bool_type_key())
            }
        );
        assert_eq!(
            ctx.get_scoped_symbol(None, "my_var").unwrap().type_key,
            ctx.bool_type_key()
        );
    }

    #[test]
    fn type_mismatch() {
        let mut ctx = ProgramContext::new_with_host_target("test", vec!["test"]);
        let var_decl = VariableDeclaration::new(
            Some(Type::new_unresolved("i64")),
            false,
            "my_string".to_string(),
            Expression::StrLiteral(StrLit::new_with_default_pos("bingo")),
            Default::default(),
        );
        AVarDecl::from(&mut ctx, &var_decl);
        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));
    }
}
