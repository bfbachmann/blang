use crate::lexer::pos::Span;
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;
use crate::Locatable;

/// Represents a return statement.
#[derive(Debug, PartialEq, Clone)]
pub struct Ret {
    pub value: Option<Expression>,
    pub span: Span,
}

locatable_impl!(Ret);

impl Ret {
    /// Creates a new return statement.
    pub fn new(value: Option<Expression>, span: Span) -> Self {
        Ret { value, span }
    }
}
