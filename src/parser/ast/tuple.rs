use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use colored::Colorize;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::r#type::Type;
use crate::parser::error::{ErrorKind, ParseError, ParseResult};
use crate::parser::module::Module;
use crate::{locatable_impl, util};

/// Represents tuple type declaration.
#[derive(Debug, Eq)]
pub struct TupleType {
    pub field_types: Vec<Type>,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(TupleType);

impl Hash for TupleType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for typ in &self.field_types {
            typ.hash(state);
        }
    }
}

impl Display for TupleType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        for (i, typ) in self.field_types.iter().enumerate() {
            write!(f, "{}", typ)?;

            if i + 1 < self.field_types.len() {
                write!(f, ", ")?;
            }
        }

        write!(f, "}}")?;

        Ok(())
    }
}

impl Clone for TupleType {
    fn clone(&self) -> Self {
        TupleType {
            field_types: self.field_types.iter().map(|t| t.clone()).collect(),
            start_pos: self.start_pos.clone(),
            end_pos: self.end_pos.clone(),
        }
    }
}

impl PartialEq for TupleType {
    fn eq(&self, other: &Self) -> bool {
        util::vecs_eq(&self.field_types, &other.field_types)
    }
}

impl TupleType {
    /// Creates a new tuple type with default start and end positions.
    pub fn new_with_default_pos(types: Vec<Type>) -> Self {
        TupleType {
            field_types: types,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Parses tuple type declarations. Expects token sequences of the form
    ///
    ///     { <type>, ... }
    ///
    /// where
    ///  - `type` is the type of the tuple field and can be repeated.
    ///
    /// Tuples can also be empty.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Record the starting position of this statement.
        let start_pos = Module::current_position(tokens);

        // The first token should be `{`.
        Module::parse_expecting(tokens, TokenKind::LeftBrace)?;

        // The next tokens should be types followed by commas ending in `}`.
        let mut types = vec![];
        let end_pos;
        loop {
            match tokens.peek_next() {
                Some(Token {
                    kind: TokenKind::Comma,
                    ..
                }) => {
                    // The comma should only come after a type.
                    return Err(ParseError::new_with_token(
                        ErrorKind::UnexpectedToken,
                        format_code!("expected type or {}", TokenKind::Comma).as_str(),
                        tokens.next().unwrap().clone(),
                    ));
                }

                Some(Token {
                    kind: TokenKind::RightBrace,
                    ..
                }) => {
                    // Record the ending position of this statement.
                    end_pos = tokens.next().unwrap().end;
                    break;
                }

                _ => {
                    // The token is not a comma or `}`, so we're expecting it to be a type.
                    let typ = Type::from(tokens)?;
                    types.push(typ);

                    // The next token should be a comma or `}`.
                    if let token @ Token {
                        kind: TokenKind::RightBrace,
                        ..
                    } = Module::parse_expecting_any(
                        tokens,
                        HashSet::from([TokenKind::Comma, TokenKind::RightBrace]),
                    )? {
                        // Record the ending position of this statement.
                        end_pos = token.end;
                        break;
                    }
                }
            }
        }

        Ok(TupleType {
            field_types: types,
            start_pos,
            end_pos,
        })
    }
}

/// Represents tuple initialization.
#[derive(Debug, Eq)]
pub struct TupleInit {
    pub values: Vec<Expression>,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(TupleInit);

impl Display for TupleInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        for (i, val) in self.values.iter().enumerate() {
            write!(f, "{}", val)?;

            if i + 1 < self.values.len() {
                write!(f, ", ")?;
            }
        }

        write!(f, "}}")?;

        Ok(())
    }
}

impl Clone for TupleInit {
    fn clone(&self) -> Self {
        TupleInit {
            values: self.values.iter().map(|v| v.clone()).collect(),
            start_pos: self.start_pos.clone(),
            end_pos: self.end_pos.clone(),
        }
    }
}

impl PartialEq for TupleInit {
    fn eq(&self, other: &Self) -> bool {
        util::vecs_eq(&self.values, &other.values)
    }
}

impl Hash for TupleInit {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.values.hash(state);
    }
}

impl TupleInit {
    /// Parses tuple initializations. Expects token sequences of the form
    ///
    ///     { <expr>, ... }
    ///
    /// where
    ///  - `expr` is and expression representing a tuple field.
    ///
    /// Tuples can also be empty.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Record the starting position of this statement.
        let start_pos = Module::current_position(tokens);

        // The first token should be `{`.
        Module::parse_expecting(tokens, TokenKind::LeftBrace)?;

        // The next tokens should be expressions followed by commas ending in `}`.
        let mut values = vec![];
        let end_pos;
        loop {
            match tokens.peek_next() {
                Some(Token {
                    kind: TokenKind::Comma,
                    ..
                }) => {
                    // The comma should only come after a type.
                    return Err(ParseError::new_with_token(
                        ErrorKind::UnexpectedToken,
                        format_code!("expected type or {}", TokenKind::Comma).as_str(),
                        tokens.next().unwrap().clone(),
                    ));
                }

                Some(Token {
                    kind: TokenKind::RightBrace,
                    ..
                }) => {
                    // Record the ending position of this statement.
                    end_pos = tokens.next().unwrap().end;
                    break;
                }

                _ => {
                    // The token is not a comma or `}`, so we're expecting it to be an expression.
                    let val = Expression::from(tokens)?;
                    values.push(val);

                    // The next token should be a comma or `}`.
                    if let token @ Token {
                        kind: TokenKind::RightBrace,
                        ..
                    } = Module::parse_expecting_any(
                        tokens,
                        HashSet::from([TokenKind::Comma, TokenKind::RightBrace]),
                    )? {
                        // Record the ending position of this statement.
                        end_pos = token.end;
                        break;
                    }
                }
            }
        }

        Ok(TupleInit {
            values,
            start_pos,
            end_pos,
        })
    }
}
