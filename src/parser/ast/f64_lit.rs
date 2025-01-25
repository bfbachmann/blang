use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::Span;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl; use crate::Locatable;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::file_parser::FileParser;

/// Represents a signed 64 bit floating-point literal.
#[derive(Debug, PartialEq, Clone)]
pub struct F64Lit {
    pub value: f64,
    /// Indicates whether the literal was declared with an explicit type suffix.
    /// For example, this would be true for the literal `123.0f64` and false for
    /// `123.0`.
    pub has_suffix: bool,
    pub span: Span,
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
    pub fn parse(parser: &mut FileParser) -> ParseResult<F64Lit> {
        match parser.tokens.next() {
            Some(&Token {
                kind: TokenKind::F64Literal((value, has_suffix)),
                span,
            }) => Ok(F64Lit {
                value,
                has_suffix,
                span,
            }),
            Some(other) => Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected {} literal, but found {}", "f64", other).as_str(),
                Some(other.clone()),
                other.span,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected f64 literal, but found EOF",
                None,
                Default::default(),
            )),
        }
    }
}
