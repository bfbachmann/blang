use std::fmt::{Display, Formatter};

use crate::lexer::pos::Span;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::r#type::Type;
use crate::parser::error::{ErrorKind, ParseError, ParseResult};
use crate::parser::file_parser::FileParser;
use crate::Locatable;
use std::hash::{Hash, Hasher};

/// Represents tuple type declaration.
#[derive(Debug, Clone, Eq)]
pub struct TupleType {
    pub field_types: Vec<Type>,
    pub span: Span,
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

impl PartialEq for TupleType {
    fn eq(&self, other: &Self) -> bool {
        self.field_types == other.field_types
    }
}

impl TupleType {
    /// Creates a new tuple type with default span.
    pub fn new_with_default_span(types: Vec<Type>) -> Self {
        TupleType {
            field_types: types,
            span: Default::default(),
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
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        // Record the starting position of this statement.
        let start_pos = parser.current_position();

        // The first token should be `{`.
        parser.parse_expecting(TokenKind::LeftBrace)?;

        // The next tokens should be types followed by commas ending in `}`.
        let mut types = vec![];
        let end_pos;
        loop {
            match parser.tokens.peek_next() {
                Some(Token {
                    kind: TokenKind::Comma,
                    ..
                }) => {
                    // The comma should only come after a type.
                    return Err(ParseError::new_with_token(
                        ErrorKind::UnexpectedToken,
                        format_code!("expected type or {}", TokenKind::Comma).as_str(),
                        parser.tokens.next().unwrap().clone(),
                    ));
                }

                Some(Token {
                    kind: TokenKind::RightBrace,
                    ..
                }) => {
                    // Record the ending position of this statement.
                    end_pos = parser.tokens.next().unwrap().span.end_pos;
                    break;
                }

                _ => {
                    // The token is not a comma or `}`, so we're expecting it to be a type.
                    let typ = Type::parse(parser)?;
                    types.push(typ);

                    // The next token should be a comma or `}`.
                    if let token @ Token {
                        kind: TokenKind::RightBrace,
                        ..
                    } =
                        parser.parse_expecting_any(vec![TokenKind::Comma, TokenKind::RightBrace])?
                    {
                        // Record the ending position of this statement.
                        end_pos = token.span.end_pos;
                        break;
                    }
                }
            }
        }

        Ok(TupleType {
            field_types: types,
            span: parser.new_span(start_pos, end_pos),
        })
    }
}

/// Represents tuple initialization.
#[derive(Debug, Eq, Clone)]
pub struct TupleInit {
    pub values: Vec<Expression>,
    pub span: Span,
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

impl PartialEq for TupleInit {
    fn eq(&self, other: &Self) -> bool {
        self.values == other.values
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
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        // Record the starting position of this statement.
        let start_pos = parser.current_position();

        // The first token should be `{`.
        parser.parse_expecting(TokenKind::LeftBrace)?;

        // The next tokens should be expressions followed by commas ending in `}`.
        let mut values = vec![];
        let end_pos;
        loop {
            match parser.tokens.peek_next() {
                Some(Token {
                    kind: TokenKind::Comma,
                    ..
                }) => {
                    // The comma should only come after a type.
                    return Err(ParseError::new_with_token(
                        ErrorKind::UnexpectedToken,
                        format_code!("expected type or {}", TokenKind::Comma).as_str(),
                        parser.tokens.next().unwrap().clone(),
                    ));
                }

                Some(Token {
                    kind: TokenKind::RightBrace,
                    ..
                }) => {
                    // Record the ending position of this statement.
                    end_pos = parser.tokens.next().unwrap().span.end_pos;
                    break;
                }

                _ => {
                    // The token is not a comma or `}`, so we're expecting it to be an expression.
                    let val = Expression::parse(parser)?;
                    values.push(val);

                    // The next token should be a comma or `}`.
                    if let token @ Token {
                        kind: TokenKind::RightBrace,
                        ..
                    } =
                        parser.parse_expecting_any(vec![TokenKind::Comma, TokenKind::RightBrace])?
                    {
                        // Record the ending position of this statement.
                        end_pos = token.span.end_pos;
                        break;
                    }
                }
            }
        }

        Ok(TupleInit {
            values,
            span: Span {
                file_id: parser.file_id,
                start_pos,
                end_pos,
            },
        })
    }
}
