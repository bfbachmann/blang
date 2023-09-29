use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::stream::Stream;

/// Represents a string literal.
#[derive(Debug, PartialEq, Clone)]
pub struct StrLit {
    pub value: String,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Display for StrLit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, r#""{}""#, self.value)
    }
}

impl Locatable for StrLit {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl StrLit {
    /// Creates a new string literal with default (zero) start and end positions.
    #[cfg(test)]
    pub fn new_with_default_pos(value: &str) -> Self {
        StrLit {
            value: value.to_string(),
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Attempts to parse a string literal from the given token sequence.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        match tokens.next() {
            Some(&Token {
                kind: TokenKind::StrLiteral(ref value),
                start,
                end,
            }) => Ok(StrLit {
                value: value.to_string(),
                start_pos: start,
                end_pos: end,
            }),
            Some(other) => Err(ParseError::new_with_token(
                ErrorKind::ExpectedBasicExpr,
                format_code!("expected boolean literal, but found {}", other).as_str(),
                other.clone(),
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
