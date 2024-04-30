use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::locatable_impl;

/// Represents a user-defined type that has not yet been resolved (i.e. is not primitive).
#[derive(Debug, Clone, Eq)]
pub struct UnresolvedType {
    pub maybe_mod_name: Option<String>,
    pub name: String,
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for UnresolvedType {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.maybe_mod_name == other.maybe_mod_name
    }
}

impl Hash for UnresolvedType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.maybe_mod_name.hash(state);
    }
}

impl Display for UnresolvedType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}",
            match &self.maybe_mod_name {
                Some(mod_name) => format!("@{mod_name}."),
                None => "".to_string(),
            },
            self.name
        )
    }
}

locatable_impl!(UnresolvedType);

impl UnresolvedType {
    /// Creates a new unresolved type with the given type name.
    pub fn new(name: &str, start_pos: Position, end_pos: Position) -> Self {
        UnresolvedType {
            maybe_mod_name: None,
            name: name.to_string(),
            start_pos,
            end_pos,
        }
    }

    /// Creates a new unresolved type with a module name.
    pub fn new_with_mod(
        maybe_mod_name: Option<String>,
        name: &str,
        start_pos: Position,
        end_pos: Position,
    ) -> UnresolvedType {
        UnresolvedType {
            maybe_mod_name,
            name: name.to_string(),
            start_pos,
            end_pos,
        }
    }

    /// Creates a new unresolved type with the given type name and default start and end positions.
    pub fn new_with_default_pos(name: &str) -> Self {
        UnresolvedType {
            maybe_mod_name: None,
            name: name.to_string(),
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Returns a new "none" type representing something that does not have a type.
    pub fn unresolved_none() -> Self {
        UnresolvedType {
            maybe_mod_name: None,
            name: "<none>".to_string(),
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }
}
