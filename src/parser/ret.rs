use crate::lexer::pos::{Locatable, Position};
use crate::locatable_impl;
use crate::parser::expr::Expression;

/// Represents a return statement.
#[derive(Debug, PartialEq, Clone)]
pub struct Ret {
    pub value: Option<Expression>,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(Ret);

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
