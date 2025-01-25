use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Span};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl; use crate::Locatable;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::file_parser::FileParser;

/// Represents a boolean literal.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BoolLit {
    pub value: bool,
    pub span: Span,
}

impl Display for BoolLit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Hash for BoolLit {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

locatable_impl!(BoolLit);

impl BoolLit {
    /// Creates a new boolean literal with default (zero) start and end positions.
    #[cfg(test)]
    pub fn new_with_default_pos(value: bool) -> Self {
        BoolLit {
            value,
            span: Default::default(),
        }
    }

    /// Creates a new boolean literal.
    #[cfg(test)]
    pub fn new(value: bool, span: Span) -> Self {
        BoolLit { value, span }
    }

    /// Attempts to parse a boolean literal from the given token sequence.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        match parser.tokens.next() {
            Some(Token {
                kind: TokenKind::BoolLiteral(value),
                span,
            }) => Ok(BoolLit {
                value: *value,
                span: span.clone(),
            }),
            Some(other) => Err(ParseError::new_with_token(
                ErrorKind::ExpectedBasicExpr,
                format_code!("expected boolean literal, but found {}", other).as_str(),
                other.clone(),
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected boolean literal, but found EOF",
                None,
                Default::default(),
            )),
        }
    }
}
