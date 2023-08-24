use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};

/// Represents a user-defined type that has not yet been resolved (i.e. is not primitive).
#[derive(Debug, Clone, Eq)]
pub struct UnresolvedType {
    pub name: String,
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for UnresolvedType {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Hash for UnresolvedType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

impl Locatable for UnresolvedType {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl UnresolvedType {
    /// Creates a new unresolved type with the given type name.
    pub fn new(name: &str, start_pos: Position, end_pos: Position) -> Self {
        UnresolvedType {
            name: name.to_string(),
            start_pos,
            end_pos,
        }
    }

    /// Creates a new unresolved type with the given type name and default start and end positions.
    pub fn new_with_default_pos(name: &str) -> Self {
        UnresolvedType {
            name: name.to_string(),
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Returns a new "unknown" type representing a type that could not be resolved.
    pub fn unknown() -> Self {
        UnresolvedType {
            name: "<unknown>".to_string(),
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Returns a new "none" type representing something that does not have a type.
    pub fn none() -> Self {
        UnresolvedType {
            name: "<none>".to_string(),
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }
}
