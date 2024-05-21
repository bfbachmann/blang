use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};

/// Represents a signed 64 bit integer literal.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct I64Lit {
    pub value: i64,
    pub span: Span,
}

impl Hash for I64Lit {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

impl Display for I64Lit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

locatable_impl!(I64Lit);

impl I64Lit {
    #[cfg(test)]
    pub fn new_with_default_pos(i: i64) -> I64Lit {
        I64Lit {
            value: i,
            span: Default::default(),
        }
    }

    /// Attempts to parse an i64 literal from the token sequence.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<I64Lit> {
        match tokens.next() {
            Some(&Token {
                kind: TokenKind::I64Literal(value),
                span,
            }) => Ok(I64Lit { value, span }),
            Some(other) => Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected {} literal, but found {}", "i64", other).as_str(),
                Some(other.clone()),
                other.span,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected i64 literal, but found EOF",
                None,
                Default::default(),
            )),
        }
    }
}
