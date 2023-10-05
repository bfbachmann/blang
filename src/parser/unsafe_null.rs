use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
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
        write!(f, "{}", TokenKind::UnsafeNull)
    }
}

locatable_impl!(UnsafeNull);

impl UnsafeNull {
    /// Attempts to parse an `UNSAFE_NULL` value from the token sequence.
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
