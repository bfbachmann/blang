use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};

/// Represents the null value of the `ptr` type.
#[derive(Debug, PartialEq, Clone)]
pub struct Null {
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Display for Null {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", TokenKind::Null)
    }
}

locatable_impl!(Null);

impl Null {
    /// Attempts to parse an `NULL` value from the token sequence.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        match tokens.next() {
            Some(&Token {
                kind: TokenKind::Null,
                start,
                end,
            }) => Ok(Null {
                start_pos: start,
                end_pos: end,
            }),
            Some(other) => Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected {}, but found {}", TokenKind::Null, other).as_str(),
                Some(other.clone()),
                other.start,
                other.end,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                format_code!("expected {}, but found EOF", TokenKind::Null).as_str(),
                None,
                Position::default(),
                Position::default(),
            )),
        }
    }
}
