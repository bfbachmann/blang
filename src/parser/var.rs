use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::member::MemberAccess;
use crate::parser::stream::Stream;

/// Represents a variable. Variables can be made via simply naming a variable or by accessing a
/// member of a variable.
#[derive(Debug, PartialEq, Clone)]
pub struct Var {
    pub var_name: String,
    pub member_access: Option<MemberAccess>,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.var_name)?;

        if let Some(ma) = &self.member_access {
            write!(f, ".{}", ma)?;
        }

        Ok(())
    }
}

impl Locatable for Var {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl Var {
    /// Creates a new variable.
    pub fn new(var_name: &str, start_pos: Position, end_pos: Position) -> Self {
        Var {
            var_name: var_name.to_string(),
            member_access: None,
            start_pos,
            end_pos,
        }
    }

    /// Creates a new variable with default (zero) start and end positions.
    #[cfg(test)]
    pub fn new_with_default_pos(var_name: &str) -> Self {
        Var {
            var_name: var_name.to_string(),
            member_access: None,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Attempts to parse a variable from the given token sequence. A variable can be an identifier
    /// representing the variable name or a type member access.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        match tokens.next() {
            Some(&Token {
                kind: TokenKind::Identifier(ref var_name),
                start,
                end,
            }) => {
                let var_name = var_name.clone();

                // Check if the next token is `.`. If so, we're accessing a member on this variable
                // or type.
                let member_access = match tokens.peek_next() {
                    Some(&Token {
                        kind: TokenKind::Dot,
                        ..
                    }) => Some(MemberAccess::from(tokens)?),
                    _ => None,
                };

                Ok(Var {
                    var_name,
                    member_access,
                    start_pos: start,
                    end_pos: end,
                })
            }

            Some(&Token {
                kind: TokenKind::This,
                start,
                end,
            }) => {
                // Check if the next token is `.`. If so, we're accessing a member on this variable
                // or type.
                let member_access = match tokens.peek_next() {
                    Some(&Token {
                        kind: TokenKind::Dot,
                        ..
                    }) => Some(MemberAccess::from(tokens)?),
                    _ => None,
                };

                Ok(Var {
                    var_name: TokenKind::This.to_string(),
                    member_access,
                    start_pos: start,
                    end_pos: end,
                })
            }

            Some(other) => Err(ParseError::new(
                ErrorKind::ExpectedIdent,
                format_code!("expected identifier, but found {}", other).as_str(),
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
