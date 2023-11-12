use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::program::Program;

/// Represents a break statement.
#[derive(Debug, PartialEq, Clone)]
pub struct Break {
    pub start_pos: Position,
    pub end_pos: Position,
}

locatable_impl!(Break);

impl Break {
    /// Parses a break statement from the given token sequence.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let token = Program::parse_expecting(tokens, TokenKind::Break)?;
        Ok(Break {
            start_pos: token.start,
            end_pos: token.end,
        })
    }
}
