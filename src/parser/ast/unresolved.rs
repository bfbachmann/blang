use std::fmt::{Display, Formatter};

use crate::fmt::vec_to_string;
use crate::lexer::pos::Span;
use crate::locatable_impl;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::symbol::{Name, Symbol};
use crate::Locatable;

/// Represents a user-defined type that has not yet been resolved (i.e. is not primitive).
#[derive(Debug, Clone)]
pub struct UnresolvedType {
    pub maybe_mod_name: Option<Name>,
    pub name: Name,
    pub params: Vec<Type>,
    pub span: Span,
}

impl PartialEq for UnresolvedType {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.maybe_mod_name == other.maybe_mod_name
            && self.params == other.params
    }
}

impl Display for UnresolvedType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}{}",
            match &self.maybe_mod_name {
                Some(sym) => format!("@{}.", sym.value),
                None => "".to_string(),
            },
            self.name,
            match self.params.len() {
                0 => "".to_string(),
                _ => format!("[{}]", vec_to_string(&self.params, ", ")),
            }
        )
    }
}

locatable_impl!(UnresolvedType);

impl UnresolvedType {
    /// Creates a new unresolved type with the given type name.
    pub fn new(name: Name, span: Span) -> Self {
        UnresolvedType {
            maybe_mod_name: None,
            name,
            params: vec![],
            span,
        }
    }

    /// Creates a new unresolved type from the given symbol.
    pub fn from_symbol(symbol: Symbol) -> UnresolvedType {
        UnresolvedType {
            maybe_mod_name: symbol.maybe_mod_name,
            name: symbol.name,
            params: symbol.params,
            span: symbol.span,
        }
    }

    /// Creates a new unresolved type with the given type name and default span.
    pub fn new_with_default_span(name: &str) -> Self {
        UnresolvedType {
            maybe_mod_name: None,
            name: Name {
                value: name.to_string(),
                span: Default::default(),
            },
            params: vec![],
            span: Default::default(),
        }
    }

    /// Returns a new "none" type representing something that does not have a type.
    pub fn unresolved_none() -> Self {
        UnresolvedType::new_with_default_span("<none>")
    }
}
