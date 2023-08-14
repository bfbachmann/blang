use colored::Colorize;
use std::collections::VecDeque;
use std::fmt::{Display, Formatter};

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::ParseResult;

/// Represents a variable reference.
#[derive(Debug, PartialEq, Clone)]
pub struct VarRef {
    pub var_name: String,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Display for VarRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.var_name)
    }
}

impl Locatable for VarRef {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl VarRef {
    /// Creates a new variable reference with default (zero) start and end positions.
    #[cfg(test)]
    pub fn new_with_default_pos(var_name: &str) -> Self {
        VarRef {
            var_name: var_name.to_string(),
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Attempts to parse a variable reference from the given token sequence.
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        match tokens.pop_front() {
            Some(Token {
                kind: TokenKind::Identifier(var_name),
                start,
                end,
            }) => Ok(VarRef {
                var_name,
                start_pos: start,
                end_pos: end,
            }),
            Some(other) => Err(ParseError::new(
                ErrorKind::ExpectedIdent,
                format!(
                    "expected identifier, but found `{}`",
                    format!("{}", other).blue()
                )
                .as_str(),
                Some(other.clone()),
                other.start,
                other.end,
            )),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected identifier, but found EOF",
                None,
                Position::default(),
                Position::default(),
            )),
        }
    }
}
