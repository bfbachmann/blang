use crate::lexer::pos::{Locatable, Position};

/// Represents a string type.
#[derive(Debug, Clone)]
pub struct StringType {
    start_pos: Position,
    end_pos: Position,
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
