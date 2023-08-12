use std::collections::VecDeque;
use std::fmt::{Display, Formatter};

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::ParseResult;

/// Represents a boolean literal.
#[derive(Debug, PartialEq, Clone)]
pub struct BoolLit {
    pub value: bool,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Display for BoolLit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Locatable for BoolLit {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl BoolLit {
    /// Creates a new boolean literal with default (zero) start and end positions.
    #[cfg(test)]
    pub fn new_with_default_pos(value: bool) -> Self {
        BoolLit {
            value,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Creates a new boolean literal.
    #[cfg(test)]
    pub fn new(value: bool, start_pos: Position, end_pos: Position) -> Self {
        BoolLit {
            value,
            start_pos,
            end_pos,
        }
    }

    /// Attempts to parse a boolean literal from the given token sequence.
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        match tokens.pop_front() {
            Some(Token {
                kind: TokenKind::BoolLiteral(value),
                start,
                end,
            }) => Ok(BoolLit {
                value,
                start_pos: start,
                end_pos: end,
            }),
            Some(other) => Err(ParseError::new_with_token(
                ErrorKind::ExpectedBasicExpr,
                format!("expected boolean literal, but found {}", other).as_str(),
                other,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected boolean literal, but found EOF",
                None,
                Position::default(),
                Position::default(),
            )),
        }
    }
}
