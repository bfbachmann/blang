use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::stream::Stream;

/// Represents the null value of the `unsafeptr` type.
#[derive(Debug, PartialEq, Clone)]
pub struct UnsafeNull {
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Display for UnsafeNull {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "unsafe_null")
    }
}

impl Locatable for UnsafeNull {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl UnsafeNull {
    /// Attempts to parse an `unsafe_null` value from the token sequence.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        match tokens.next() {
            Some(&Token {
                kind: TokenKind::UnsafeNull,
                start,
                end,
            }) => Ok(UnsafeNull {
                start_pos: start,
                end_pos: end,
            }),
            Some(other) => Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected {}, but found {}", TokenKind::UnsafeNull, other).as_str(),
                Some(other.clone()),
                other.start,
                other.end,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                format_code!("expected {}, but found EOF", TokenKind::UnsafeNull).as_str(),
                None,
                Position::default(),
                Position::default(),
            )),
        }
    }
}
