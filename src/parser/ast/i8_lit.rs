use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::Span;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a signed 8 bit integer literal.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct I8Lit {
    pub value: i8,
    pub span: Span,
}

impl Display for I8Lit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Hash for I8Lit {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

locatable_impl!(I8Lit);

impl I8Lit {
    /// Attempts to parse an i8 literal from the token sequence.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        match parser.tokens.next() {
            Some(&Token {
                kind: TokenKind::I8Literal(value),
                span,
            }) => Ok(I8Lit { value, span }),
            Some(other) => Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected {} literal, but found {}", "i8", other).as_str(),
                Some(other.clone()),
                other.span,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected i8 literal, but found EOF",
                None,
                Default::default(),
            )),
        }
    }
}
