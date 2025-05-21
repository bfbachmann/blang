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

/// Represents an unsigned 32 bit integer literal.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct U32Lit {
    pub value: u32,
    pub span: Span,
}

impl Display for U32Lit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Hash for U32Lit {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

locatable_impl!(U32Lit);

impl U32Lit {
    /// Attempts to parse an u32 literal from the token sequence.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        match parser.tokens.next() {
            Some(&Token {
                kind: TokenKind::U32Literal(value),
                span,
            }) => Ok(U32Lit { value, span }),
            Some(other) => Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected {} literal, but found {}", "u32", other).as_str(),
                Some(other.clone()),
                other.span,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected u32 literal, but found EOF",
                None,
                Default::default(),
            )),
        }
    }
}
