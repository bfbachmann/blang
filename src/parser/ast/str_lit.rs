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

/// Represents a string literal.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct StrLit {
    pub value: String,
    pub span: Span,
}

impl Hash for StrLit {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

impl Display for StrLit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, r#""{}""#, self.value)
    }
}

locatable_impl!(StrLit);

impl StrLit {
    /// Attempts to parse a string literal from the given token sequence.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        match parser.tokens.next() {
            Some(&Token {
                kind: TokenKind::StrLiteral(ref value),
                span,
            }) => Ok(StrLit {
                value: value.to_string(),
                span,
            }),
            Some(other) => Err(ParseError::new_with_token(
                ErrorKind::ExpectedBasicExpr,
                format_code!("expected string literal, but found {}", other).as_str(),
                other.clone(),
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected string literal, but found EOF",
                None,
                Default::default(),
            )),
        }
    }
}
