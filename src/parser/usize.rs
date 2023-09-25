use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};

/// Represents a pointer-sized unsigned integer.
#[derive(Debug, Clone, Eq)]
pub struct USizeType {
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for USizeType {
    fn eq(&self, _other: &Self) -> bool {
        // Two usize types are always considered equal.
        true
    }
}

impl Hash for USizeType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "usize".hash(state);
    }
}

impl Locatable for USizeType {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl USizeType {
    pub fn new(start_pos: Position, end_pos: Position) -> Self {
        USizeType { start_pos, end_pos }
    }

    pub fn default() -> Self {
        USizeType {
            start_pos: Default::default(),
            end_pos: Default::default(),
        }
    }
}
