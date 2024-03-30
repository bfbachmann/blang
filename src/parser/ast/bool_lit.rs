use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};

/// Represents a boolean literal.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BoolLit {
    pub value: bool,
    pub start_pos: Position,
    pub end_pos: Position,
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
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Creates a new boolean literal.
    #[cfg(test)]
    pub fn new(value: bool, start_pos: Position, end_pos: Position) -> Self {
        BoolLit {
            value,
            start_pos,
            end_pos,
        }
    }

    /// Attempts to parse a boolean literal from the given token sequence.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        match tokens.next() {
            Some(Token {
                kind: TokenKind::BoolLiteral(value),
                start,
                end,
            }) => Ok(BoolLit {
                value: *value,
                start_pos: start.clone(),
                end_pos: end.clone(),
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
                Position::default(),
                Position::default(),
            )),
        }
    }
}
