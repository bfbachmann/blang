use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};

/// Represents a signed 64 bit floating-point literal.
#[derive(Debug, PartialEq, Clone)]
pub struct F64Lit {
    pub value: f64,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Eq for F64Lit {
    fn assert_receiver_is_total_eq(&self) {}
}

impl Hash for F64Lit {
    fn hash<H: Hasher>(&self, _: &mut H) {}
}

impl Display for F64Lit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

locatable_impl!(F64Lit);

impl F64Lit {
    /// Attempts to parse a f64 literal from the token sequence.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<F64Lit> {
        match tokens.next() {
            Some(&Token {
                kind: TokenKind::F64Literal(value),
                start,
                end,
            }) => Ok(F64Lit {
                value,
                start_pos: start,
                end_pos: end,
            }),
            Some(other) => Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected {} literal, but found {}", "f64", other).as_str(),
                Some(other.clone()),
                other.start,
                other.end,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected f64 literal, but found EOF",
                None,
                Position::default(),
                Position::default(),
            )),
        }
    }
}
