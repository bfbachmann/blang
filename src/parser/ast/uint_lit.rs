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
pub struct UintLit {
    pub value: u64,
    pub span: Span,
}

impl Display for UintLit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Hash for UintLit {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

locatable_impl!(UintLit);

impl UintLit {
    pub fn new_with_default_pos(u: u64) -> UintLit {
        UintLit {
            value: u,
            span: Default::default(),
        }
    }

    /// Attempts to parse a `uint` literal from the token sequence.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        match tokens.next() {
            Some(&Token {
                kind: TokenKind::UintLiteral(value),
                span,
            }) => Ok(UintLit { value, span }),
            Some(other) => Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected {} literal, but found {}", "uint", other).as_str(),
                Some(other.clone()),
                other.span,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected uint literal, but found EOF",
                None,
                Default::default(),
            )),
        }
    }
}
