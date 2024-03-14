use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use colored::Colorize;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};

/// Represents a signed 64 bit integer literal.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IntLit {
    pub value: i64,
    pub start_pos: Position,
    pub end_pos: Position,
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
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<IntLit> {
        match tokens.next() {
            Some(&Token {
                kind: TokenKind::IntLiteral(value),
                start,
                end,
            }) => Ok(IntLit {
                value,
                start_pos: start,
                end_pos: end,
            }),
            Some(other) => Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected {} literal, but found {}", "int", other).as_str(),
                Some(other.clone()),
                other.start,
                other.end,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected int literal, but found EOF",
                None,
                Position::default(),
                Position::default(),
            )),
        }
    }
}
