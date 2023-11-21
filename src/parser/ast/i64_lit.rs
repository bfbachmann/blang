use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};

/// Represents a signed 64 bit integer literal.
#[derive(Debug, PartialEq, Clone)]
pub struct I64Lit {
    pub value: i64,
    /// Will be true if the i64 literal in the source code included the explicit "i64" suffix.
    pub has_type_suffix: bool,
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
    pub fn new_with_default_pos(i: i64) -> I64Lit {
        I64Lit {
            value: i,
            has_type_suffix: false,
            start_pos: Default::default(),
            end_pos: Default::default(),
        }
    }

    /// Attempts to parse an i64 literal from the token sequence.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<I64Lit> {
        match tokens.next() {
            Some(&Token {
                kind: TokenKind::I64Literal(value, has_type_suffix),
                start,
                end,
            }) => Ok(I64Lit {
                value,
                has_type_suffix,
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
