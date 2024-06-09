use crate::lexer::pos::Position;
use crate::lexer::pos::{Locatable, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::statement::Statement;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

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
    ///
    /// where
    /// - `statement` is a closure, conditional, or loop statement
    ///   (see `Statement::from`).
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<From> {
        let start_pos = Module::parse_expecting(tokens, TokenKind::From)?
            .span
            .start_pos;

        // The next statement should be a closure, conditional, or loop.
        Module::parse_expecting_any(
            tokens,
            vec![TokenKind::LeftBrace, TokenKind::If, TokenKind::Loop],
        )?;
        tokens.rewind(1);

        let statement = Box::new(Statement::from(tokens)?);

        Ok(From {
            span: Span {
                start_pos,
                end_pos: statement.end_pos().clone(),
            },
            statement,
        })
    }
}
