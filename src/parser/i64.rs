use crate::lexer::pos::{Locatable, Position};
use std::hash::{Hash, Hasher};

/// Represents a 64 bit signed integer type.
#[derive(Debug, Clone, Eq)]
pub struct I64Type {
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for I64Type {
    fn eq(&self, _other: &Self) -> bool {
        // Two i64 types are always considered equal.
        true
    }
}

impl Hash for I64Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "i64".hash(state);
    }
}

impl Locatable for I64Type {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl I64Type {
    pub fn new(start_pos: Position, end_pos: Position) -> Self {
        I64Type { start_pos, end_pos }
    }

    pub fn default() -> Self {
        I64Type {
            start_pos: Default::default(),
            end_pos: Default::default(),
        }
    }
}
