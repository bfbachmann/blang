use std::fmt;
use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::error::{err_dup_ident, err_not_const};
use crate::analyzer::ident::Ident;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::{Locatable, Span};
use crate::parser::ast::r#const::Const;
use crate::parser::ast::r#type::Type;
use crate::util;

/// Represents a semantically valid constant declaration.
#[derive(Debug, Clone)]
pub struct AConst {
    pub name: String,
    pub declared_type_key: Option<TypeKey>,
    pub value: AExpr,
    pub span: Span,
}

impl PartialEq for AConst {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && util::opts_eq(&self.declared_type_key, &other.declared_type_key)
            && self.value == other.value
    }
}

impl Display for AConst {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.name)?;

        if let Some(typ) = &self.declared_type_key {
            write!(f, ": {}", typ)?;
        }

        write!(f, " = {}", self.value)
    }
}

impl AConst {
    /// Analyzes a const declaration and returns a semantically valid, type-rich constant
    /// declaration.
    pub fn from(ctx: &mut ProgramContext, const_decl: &Const) -> Self {
        // Analyze the optional constant type.
        let declared_tk = match &const_decl.maybe_type {
            Some(typ) => Some(ctx.resolve_type(typ)),
            None => None,
        };

        // Make sure the constant value is a valid constant.
        let value = AExpr::from(ctx, const_decl.value.clone(), declared_tk, false, false);

        // Add the identifier to the program context so it can be used later.
        if let Err(existing) = ctx.insert_ident(Ident::new_const(
            const_decl.name.value.clone(),
            const_decl.is_pub,
            value.clone(),
            Some(ctx.cur_mod_id()),
            const_decl.name.span,
        )) {
            let err = err_dup_ident(&existing.name, const_decl.span, existing.span);
            ctx.insert_err(err);
        }

        // Just return a dummy value if the expression already failed analysis.
        if ctx.get_type(value.type_key).is_unknown() {
            return AConst::new_zero_value(ctx, const_decl.name.value.as_str());
        }

        // Error if the value assigned to the constant is not constant.
        if !value.kind.is_const() {
            ctx.insert_err(err_not_const(ctx, &value));
            return AConst::new_zero_value(ctx, const_decl.name.value.as_str());
        }

        AConst {
            name: const_decl.name.value.clone(),
            declared_type_key: declared_tk,
            value,
            span: const_decl.span().clone(),
        }
    }

    /// Creates a new constant with the given name and a default value.
    fn new_zero_value(ctx: &mut ProgramContext, name: &str) -> Self {
        AConst {
            name: name.to_string(),
            declared_type_key: None,
            value: AExpr::new_zero_value(ctx, Type::new_unresolved("<unknown>")),
            span: Default::default(),
        }
    }
}
