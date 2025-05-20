use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::error::err_dup_ident;
use crate::analyzer::ident::Ident;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::Span;
use crate::parser::ast::var_dec::VariableDeclaration;

/// Represents a semantically valid and type-rich variable declaration.
#[derive(PartialEq, Debug, Clone)]
pub struct AVarDecl {
    pub type_key: TypeKey,
    pub name: String,
    pub val: AExpr,
    pub span: Span,
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
        let maybe_declared_tk = var_decl.maybe_type.as_ref().map(|typ| ctx.resolve_type(typ));

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
        if let Err(existing) = ctx.insert_ident(Ident::new_var(
            var_decl.name.value.clone(),
            var_decl.is_mut,
            type_key,
            var_decl.name.span,
        )) {
            let existing_span = existing.span;
            ctx.insert_err(err_dup_ident(
                &var_decl.name.value,
                var_decl.name.span,
                existing_span,
            ));
        };

        AVarDecl {
            type_key,
            name: var_decl.name.value.clone(),
            val: rich_expr,
            span: var_decl.span,
        }
    }
}
