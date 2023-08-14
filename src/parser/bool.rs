use crate::lexer::pos::{Locatable, Position};

/// Represents a boolean type.
#[derive(Debug, Clone)]
pub struct BoolType {
    start_pos: Position,
    end_pos: Position,
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
