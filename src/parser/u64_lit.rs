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
pub struct U64Lit {
    pub value: u64,
    /// Will be true if the u64 literal in the source code included the explicit "u64" suffix.
    pub has_type_suffix: bool,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Display for U64Lit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

locatable_impl!(U64Lit);

impl U64Lit {
    /// Attempts to parse an u64 literal from the token sequence.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        match tokens.next() {
            Some(&Token {
                kind: TokenKind::U64Literal(value, has_type_suffix),
                start,
                end,
            }) => Ok(U64Lit {
                value,
                has_type_suffix,
                start_pos: start,
                end_pos: end,
            }),
            Some(other) => Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected {} literal, but found {}", "u64", other).as_str(),
                Some(other.clone()),
                other.start,
                other.end,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected u64 literal, but found EOF",
                None,
                Position::default(),
                Position::default(),
            )),
        }
    }
}
