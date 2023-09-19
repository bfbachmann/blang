use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};

/// Represents a string type.
#[derive(Debug, Clone, Eq)]
pub struct StringType {
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for StringType {
    fn eq(&self, _other: &Self) -> bool {
        // Two string types are always considered equal.
        true
    }
}

impl Hash for StringType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "string".hash(state);
    }
}

impl Locatable for StringType {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl StringType {
    pub fn new(start_pos: Position, end_pos: Position) -> Self {
        StringType { start_pos, end_pos }
    }

    pub fn default() -> Self {
        StringType {
            start_pos: Default::default(),
            end_pos: Default::default(),
        }
    }
}
