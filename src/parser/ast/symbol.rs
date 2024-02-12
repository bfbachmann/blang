use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use colored::Colorize;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::member::MemberAccess;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::source::Source;

/// Represents a a named value. These can be variables, variable member accesses, functions,
/// constants, or types.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Symbol {
    pub name: String,
    pub member_access: Option<MemberAccess>,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;

        if let Some(ma) = &self.member_access {
            write!(f, ".{}", ma)?;
        }

        Ok(())
    }
}

impl Hash for Symbol {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.member_access.hash(state);
    }
}

locatable_impl!(Symbol);

impl Symbol {
    /// Creates a new symbol.
    pub fn new(name: &str, start_pos: Position, end_pos: Position) -> Self {
        Symbol {
            name: name.to_string(),
            member_access: None,
            start_pos,
            end_pos,
        }
    }

    /// Creates a new symbol with default (zero) start and end positions.
    #[cfg(test)]
    pub fn new_with_default_pos(name: &str) -> Self {
        Symbol {
            name: name.to_string(),
            member_access: None,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Attempts to parse a symbol composed only of a single identifier from the given token sequence.
    pub fn from_identifier(tokens: &mut Stream<Token>) -> ParseResult<Symbol> {
        let start_pos = Source::current_position(tokens);
        let name = Source::parse_identifier(tokens)?;
        Ok(Symbol {
            name,
            member_access: None,
            start_pos,
            end_pos: Source::prev_position(tokens),
        })
    }

    /// Attempts to parse a symbol from the given token sequence. A symbol can be an identifier
    /// representing a variable, constant, type, or function, or a type member access.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Symbol> {
        match tokens.next() {
            Some(&Token {
                kind: TokenKind::Identifier(ref name),
                start,
                end,
            }) => {
                let name = name.clone();

                // Check if the next token is `.`. If so, we're accessing a member on this variable
                // or type.
                let member_access = match tokens.peek_next() {
                    Some(&Token {
                        kind: TokenKind::Dot,
                        ..
                    }) => Some(MemberAccess::from(tokens)?),
                    _ => None,
                };

                Ok(Symbol {
                    name,
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
