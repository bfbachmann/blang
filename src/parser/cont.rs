use std::collections::{HashSet, VecDeque};

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::error::ParseResult;
use crate::parser::program::Program;

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
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        let token = Program::parse_expecting(tokens, HashSet::from([TokenKind::Continue]))?;
        Ok(Continue {
            start_pos: token.start,
            end_pos: token.end,
        })
    }
}
