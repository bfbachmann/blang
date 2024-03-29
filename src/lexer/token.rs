use std::fmt;

use crate::lexer::pos::Position;
use crate::lexer::token_kind::TokenKind;

/// A token has a kind and a start and end position (in the file).
#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub start: Position,
    pub end: Position,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}
