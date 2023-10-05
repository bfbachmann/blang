use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::stream::Stream;

/// Represents a signed 64 bit integer literal.
#[derive(Debug, PartialEq, Clone)]
pub struct I64Lit {
    pub value: i64,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Display for I64Lit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

locatable_impl!(I64Lit);

impl I64Lit {
    /// Creates a new i64 literal with default (zero) start and end positions.
    pub fn new_with_default_pos(value: i64) -> Self {
        I64Lit {
            value,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Attempts to parse an i64 literal from the token sequence.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        match tokens.next() {
            Some(&Token {
                kind: TokenKind::I64Literal(value),
                start,
                end,
            }) => Ok(I64Lit {
                value,
                start_pos: start,
                end_pos: end,
            }),
            Some(other) => Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected {} literal, but found {}", "i64", other).as_str(),
                Some(other.clone()),
                other.start,
                other.end,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected i64 literal, but found EOF",
                None,
                Position::default(),
                Position::default(),
            )),
        }
    }
}
