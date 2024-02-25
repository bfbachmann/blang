use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use std::hash::Hash;

use crate::lexer::pos::Locatable;
use crate::lexer::pos::Position;
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::i64_lit::I64Lit;
use crate::parser::ast::r#type::Type;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

/// A fixed-sized sequence of values of the same type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayType {
    pub maybe_element_type: Option<Type>,
    pub length_expr: Expression,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(ArrayType);

impl Display for ArrayType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.maybe_element_type {
            Some(typ) => {
                write!(f, "[{}; {}]", typ, self.length_expr)
            }
            None => write!(f, "[]"),
        }
    }
}

impl ArrayType {
    /// Parses an array type from the token stream. Expects token sequences of the form
    ///
    ///     `[<type>; <length>]`
    ///
    /// where
    /// - `type` is the type contained by the array (see `Type::from`)
    /// - `length` is a constant expression yielding the length of the array (see
    ///   `Expression::from`).
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<ArrayType> {
        let start_pos = Module::parse_expecting(tokens, TokenKind::LeftBracket)?.start;

        // The array type may be empty.
        if let Some(token) = Module::parse_optional(tokens, TokenKind::RightBracket) {
            return Ok(ArrayType {
                maybe_element_type: None,
                length_expr: Expression::I64Literal(I64Lit::new_with_default_pos(0)),
                start_pos,
                end_pos: token.end.clone(),
            });
        }

        let element_type = Type::from(tokens)?;
        Module::parse_expecting(tokens, TokenKind::SemiColon)?;
        let length_expr = Expression::from(tokens)?;
        let end_pos = Module::parse_expecting(tokens, TokenKind::RightBracket)?.end;

        Ok(ArrayType {
            maybe_element_type: Some(element_type),
            length_expr,
            start_pos,
            end_pos,
        })
    }
}

/// Array initialization.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayInit {
    pub values: Vec<Expression>,
    pub maybe_repeat_expr: Option<Expression>,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(ArrayInit);

impl Display for ArrayInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;

        for (i, value) in self.values.iter().enumerate() {
            match i {
                0 => write!(f, "{}", value)?,
                _ => write!(f, ", {}", value)?,
            };
        }

        if let Some(expr) = &self.maybe_repeat_expr {
            write!(f, "; {}", expr)?;
        }

        write!(f, "]")
    }
}

impl ArrayInit {
    /// Creates a new empty array initialization.
    pub fn new_empty() -> ArrayInit {
        ArrayInit {
            values: vec![],
            maybe_repeat_expr: None,
            start_pos: Default::default(),
            end_pos: Default::default(),
        }
    }

    /// Parses array initialization. Expects token sequences of the forms
    ///
    ///     `[<expr>, ...]`
    ///     `[<expr>; <repeat_count>]`
    ///     `[]`
    ///
    /// where
    /// - `expr` is an expression that can be repeated zero or more times separated by commas
    /// - `repeat_count` is a constant expression representing the number of times to repeat the
    ///   expression prior in the array.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<ArrayInit> {
        let start_pos = Module::parse_expecting(tokens, TokenKind::LeftBracket)?.start;

        // Handle the case of an empty array.
        if let Some(Token { end, .. }) = Module::parse_optional(tokens, TokenKind::RightBracket) {
            return Ok(ArrayInit {
                values: vec![],
                maybe_repeat_expr: None,
                start_pos,
                end_pos: end.clone(),
            });
        }

        // Parse the first value in the array (there must be at least one at this point).
        let mut values = vec![Expression::from(tokens)?];
        let mut maybe_repeat_expr = None;

        // Parse the rest of the values in the array, or the `; <repeat_count>`, or `]`.
        let end_pos = match Module::parse_expecting_any(
            tokens,
            HashSet::from([
                TokenKind::Comma,
                TokenKind::SemiColon,
                TokenKind::RightBracket,
            ]),
        ) {
            Ok(Token {
                kind: TokenKind::Comma,
                ..
            }) => loop {
                // Parse the expression for the next value in the array.
                values.push(Expression::from(tokens)?);

                // The next token should either be `,` or `]`.
                match Module::parse_expecting_any(
                    tokens,
                    HashSet::from([TokenKind::Comma, TokenKind::RightBracket]),
                ) {
                    Ok(Token {
                        kind: TokenKind::RightBracket,
                        end,
                        ..
                    }) => break end.clone(),

                    Ok(Token {
                        kind: TokenKind::Comma,
                        end,
                        ..
                    }) => {
                        // Handle the trailing comma.
                        if Module::parse_optional(tokens, TokenKind::RightBracket).is_some() {
                            break end.clone();
                        }
                    }

                    Err(err) => return Err(err),

                    _ => unreachable!(),
                }
            },

            Ok(Token {
                kind: TokenKind::RightBracket,
                end,
                ..
            }) => {
                // Nothing to do here. It's the end of the array.
                end
            }

            Ok(_) => {
                maybe_repeat_expr = Some(Expression::from(tokens)?);
                Module::parse_expecting(tokens, TokenKind::RightBracket)?
                    .end
                    .clone()
            }

            Err(err) => return Err(err),
        };

        Ok(ArrayInit {
            values,
            maybe_repeat_expr,
            start_pos,
            end_pos,
        })
    }
}
