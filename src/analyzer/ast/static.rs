use std::fmt;
use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::error::{err_dup_ident, err_invalid_statement, err_not_const};
use crate::analyzer::ident::Ident;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::{Locatable, Span};
use crate::parser::ast::r#static::Static;
use crate::parser::ast::r#type::Type;

/// Represents a semantically valid constant declaration.
#[derive(Debug, Clone)]
pub struct AStatic {
    pub name: String,
    pub declared_type_key: Option<TypeKey>,
    pub value: AExpr,
    pub span: Span,
}

impl PartialEq for AStatic {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.declared_type_key == other.declared_type_key
            && self.value == other.value
    }
}

impl Display for AStatic {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.name)?;

        if let Some(typ) = &self.declared_type_key {
            write!(f, ": {}", typ)?;
        }

        write!(f, " = {}", self.value)
    }
}

impl AStatic {
    /// Analyzes a `static` declaration.
    pub fn from(ctx: &mut ProgramContext, static_decl: &Static) -> Self {
        // Static declarations are only allowed at the top level.
        if ctx.is_in_fn() {
            ctx.insert_err(err_invalid_statement(static_decl.span));
            return AStatic::new_zero_value(ctx, static_decl.name.value.as_str());
        }

        // Analyze the optional type.
        let declared_tk = static_decl
            .maybe_type
            .as_ref()
            .map(|typ| ctx.resolve_type(typ));

        // Make sure the value is a valid constant.
        let value = AExpr::from(ctx, static_decl.value.clone(), declared_tk, false, false);

        // Add the identifier to the program context so it can be used later.
        if let Err(existing) = ctx.insert_ident(Ident::new_static(
            static_decl.name.value.clone(),
            static_decl.is_pub,
            static_decl.is_mut,
            value.clone(),
            Some(ctx.cur_mod_id()),
            static_decl.name.span,
        )) {
            let err = err_dup_ident(&existing.name, static_decl.span, existing.span);
            ctx.insert_err(err);
        }

        // Just return a dummy value if the expression already failed analysis.
        if ctx.get_type(value.type_key).is_unknown() {
            return AStatic::new_zero_value(ctx, static_decl.name.value.as_str());
        }

        // Error if the value assigned is not constant.
        if !value.kind.is_const() {
            ctx.insert_err(err_not_const(ctx, &value));
        }

        AStatic {
            name: static_decl.name.value.clone(),
            declared_type_key: declared_tk,
            value,
            span: *static_decl.span(),
        }
    }

    /// Creates a new static with the given name and a default value.
    fn new_zero_value(ctx: &mut ProgramContext, name: &str) -> Self {
        AStatic {
            name: name.to_string(),
            declared_type_key: None,
            value: AExpr::new_zero_value(ctx, Type::new_unresolved("<unknown>")),
            span: Default::default(),
        }
    }
}
