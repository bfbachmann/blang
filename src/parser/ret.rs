use crate::lexer::pos::{Locatable, Position};
use crate::parser::expr::Expression;

/// Represents a return statement.
#[derive(Debug, PartialEq, Clone)]
pub struct Ret {
    pub value: Option<Expression>,
    start_pos: Position,
    end_pos: Position,
}

impl Locatable for Ret {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl Ret {
    /// Creates a new return statement.
    pub fn new(value: Option<Expression>, start_pos: Position, end_pos: Position) -> Self {
        Ret {
            value,
            start_pos,
            end_pos,
        }
    }
}
