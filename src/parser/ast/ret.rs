use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;

/// Represents a return statement.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Ret {
    pub value: Option<Expression>,
    start_pos: Position,
    end_pos: Position,
}

impl Hash for Ret {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
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
