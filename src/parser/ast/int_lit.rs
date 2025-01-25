use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::Span;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl; use crate::Locatable;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::file_parser::FileParser;

/// Represents a signed 64 bit integer literal.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IntLit {
    pub value: i64,
    /// Indicates whether the literal was declared with an explicit type suffix.
    /// For example, this would be true for the literal `123int` and false for
    /// `123`.
    pub has_suffix: bool,
    pub span: Span,
}

impl Hash for IntLit {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

impl Display for IntLit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

locatable_impl!(IntLit);

impl IntLit {
    /// Attempts to parse an `int` literal from the token sequence.
    pub fn parse(parser: &mut FileParser) -> ParseResult<IntLit> {
        match parser.tokens.next() {
            Some(&Token {
                kind: TokenKind::IntLiteral((value, has_suffix)),
                span,
            }) => Ok(IntLit {
                value,
                has_suffix,
                span,
            }),
            Some(other) => Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected {} literal, but found {}", "int", other).as_str(),
                Some(other.clone()),
                other.span,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected int literal, but found EOF",
                None,
                Default::default(),
            )),
        }
    }
}
