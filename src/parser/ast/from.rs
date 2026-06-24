use crate::lexer::pos::Span;
use crate::locatable_impl;
use crate::parser::ast::statement::Statement;
use crate::Locatable;

/// Represents a statement that yields a result. This language construct exists
/// so statements can be used as expressions. There is no special syntax for this
/// AST node. It's just here so the parser can easily tell the analyzer where it
/// expected an expression but found a statement that could be valid in place of
/// an expression if it yields a valid set of values.
#[derive(Debug, PartialEq, Clone)]
pub struct From {
    pub statement: Box<Statement>,
    pub span: Span,
}

locatable_impl!(From);
