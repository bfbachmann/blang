use crate::lexer::pos::Span;
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;
use crate::Locatable;

/// Represents the yielding of a value from a statement. This is essentially like
/// a `return`, except it returns from a `from` block instead of a function, and
/// must have a value.
#[derive(Debug, PartialEq, Clone)]
pub struct Yield {
    pub value: Expression,
    pub span: Span,
}

locatable_impl!(Yield);

impl Yield {
    /// Creates a new `yield` statement.
    pub fn new(value: Expression, span: Span) -> Self {
        Yield { value, span }
    }
}
