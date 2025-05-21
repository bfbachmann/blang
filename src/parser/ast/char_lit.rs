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

/// Represents a character literal.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CharLit {
    pub value: char,
    pub span: Span,
}

impl Hash for CharLit {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

impl Display for CharLit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "'{}'", self.value)
    }
}

locatable_impl!(CharLit);

impl CharLit {
    /// Attempts to parse a character literal from the given token sequence.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        match parser.tokens.next() {
            Some(&Token {
                kind: TokenKind::CharLiteral(value),
                span,
            }) => Ok(CharLit { value, span }),
            Some(other) => Err(ParseError::new_with_token(
                ErrorKind::ExpectedBasicExpr,
                format_code!("expected character literal, but found {}", other).as_str(),
                other.clone(),
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected character literal, but found EOF",
                None,
                Default::default(),
            )),
        }
    }
}
