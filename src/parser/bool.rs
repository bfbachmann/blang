use crate::lexer::pos::{Locatable, Position};
use std::hash::{Hash, Hasher};

/// Represents a boolean type.
#[derive(Debug, Clone, Eq)]
pub struct BoolType {
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for BoolType {
    fn eq(&self, _other: &Self) -> bool {
        // Two boolean types are always considered equal.
        true
    }
}

impl Hash for BoolType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "bool".hash(state);
    }
}

impl Locatable for BoolType {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl BoolType {
    pub fn new(start_pos: Position, end_pos: Position) -> Self {
        BoolType { start_pos, end_pos }
    }

    pub fn default() -> Self {
        BoolType {
            start_pos: Default::default(),
            end_pos: Default::default(),
        }
    }
}
