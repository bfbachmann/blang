use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;

/// Represents a return statement.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Ret {
    pub value: Option<Expression>,
    span: Span,
}

impl Hash for Ret {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

locatable_impl!(Ret);

impl Ret {
    /// Creates a new return statement.
    pub fn new(value: Option<Expression>, span: Span) -> Self {
        Ret { value, span }
    }
}
