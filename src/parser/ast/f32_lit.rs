use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};

/// Represents an unsigned 32 bit floating-point literal.
#[derive(Debug, PartialEq, Clone)]
pub struct F32Lit {
    pub value: f32,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Eq for F32Lit {
    fn assert_receiver_is_total_eq(&self) {}
}

impl Display for F32Lit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}f32", self.value)
    }
}

impl Hash for F32Lit {
    fn hash<H: Hasher>(&self, _: &mut H) {}
}

locatable_impl!(F32Lit);

impl F32Lit {
    /// Attempts to parse a f32 literal from the token sequence.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        match tokens.next() {
            Some(&Token {
                kind: TokenKind::F32Literal(value),
                start,
                end,
            }) => Ok(F32Lit {
                value,
                start_pos: start,
                end_pos: end,
            }),
            Some(other) => Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected {} literal, but found {}", "f32", other).as_str(),
                Some(other.clone()),
                other.start,
                other.end,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected f32 literal, but found EOF",
                None,
                Position::default(),
                Position::default(),
            )),
        }
    }
}
