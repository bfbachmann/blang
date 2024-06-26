use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};

/// Represents an unsigned 8 bit integer literal.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct U8Lit {
    pub value: u8,
    pub span: Span,
}

impl Display for U8Lit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Hash for U8Lit {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

locatable_impl!(U8Lit);

impl U8Lit {
    /// Attempts to parse an u8 literal from the token sequence.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        match tokens.next() {
            Some(&Token {
                kind: TokenKind::U8Literal(value),
                span,
            }) => Ok(U8Lit { value, span }),
            Some(other) => Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected {} literal, but found {}", "u8", other).as_str(),
                Some(other.clone()),
                other.span,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected u8 literal, but found EOF",
                None,
                Default::default(),
            )),
        }
    }
}
