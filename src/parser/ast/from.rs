use crate::lexer::pos::Span;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::statement::Statement;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a statement that yields a result. This language construct exists
/// so statements can be used as expressions.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct From {
    pub statement: Box<Statement>,
    pub span: Span,
}

locatable_impl!(From);

impl From {
    /// Parses a `from` block from the token stream. Expects token sequences of
    /// the form
    ///
    ///     from <statement>
    pub fn from(parser: &mut FileParser) -> ParseResult<From> {
        let start_pos = parser.parse_expecting(TokenKind::From)?.span.start_pos;

        let statement = Box::new(Statement::parse(parser)?);

        Ok(From {
            span: parser.new_span(start_pos, statement.span().end_pos),
            statement,
        })
    }
}
