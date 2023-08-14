use crate::lexer::pos::{Locatable, Position};

/// Represents a 64 bit signed integer type.
#[derive(Debug, Clone)]
pub struct I64Type {
    start_pos: Position,
    end_pos: Position,
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
