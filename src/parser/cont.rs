use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::error::ParseResult;
use crate::parser::program::Program;
use crate::parser::stream::Stream;

/// Represents a continue statement.
#[derive(PartialEq, Debug, Clone)]
pub struct Continue {
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Locatable for Continue {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl Continue {
    /// Parses a continue statement from the given token sequence.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let token = Program::parse_expecting(tokens, TokenKind::Continue)?;
        Ok(Continue {
            start_pos: token.start,
            end_pos: token.end,
        })
    }
}
