use std::fmt::{Display, Formatter};
use std::hash::Hash;

use crate::lexer::pos::Position;
use crate::lexer::pos::{Locatable, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::uint_lit::UintLit;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

/// A fixed-sized sequence of values of the same type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayType {
    pub maybe_element_type: Option<Type>,
    pub length_expr: Expression,
    pub span: Span,
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
        let start_pos = Module::parse_expecting(tokens, TokenKind::LeftBracket)?
            .span
            .start_pos;

        // The array type may be empty.
        if let Some(token) = Module::parse_optional(tokens, TokenKind::RightBracket) {
            return Ok(ArrayType {
                maybe_element_type: None,
                length_expr: Expression::UintLiteral(UintLit::new_with_default_pos(0)),
                span: Span {
                    start_pos,
                    end_pos: token.span.end_pos.clone(),
                },
            });
        }

        let element_type = Type::from(tokens)?;
        Module::parse_expecting(tokens, TokenKind::SemiColon)?;
        let length_expr = Expression::from(tokens)?;
        let end_pos = Module::parse_expecting(tokens, TokenKind::RightBracket)?
            .span
            .end_pos;

        Ok(ArrayType {
            maybe_element_type: Some(element_type),
            length_expr,
            span: Span { start_pos, end_pos },
        })
    }
}

/// Array initialization.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayInit {
    pub values: Vec<Expression>,
    pub maybe_repeat_expr: Option<Expression>,
    pub span: Span,
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
            span: Default::default(),
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
        let start_pos = Module::parse_expecting(tokens, TokenKind::LeftBracket)?
            .span
            .start_pos;

        // Handle the case of an empty array.
        if let Some(Token { span, .. }) = Module::parse_optional(tokens, TokenKind::RightBracket) {
            return Ok(ArrayInit {
                values: vec![],
                maybe_repeat_expr: None,
                span: Span {
                    start_pos,
                    end_pos: span.end_pos,
                },
            });
        }

        // Parse the first value in the array (there must be at least one at this point).
        let mut values = vec![Expression::from(tokens)?];
        let mut maybe_repeat_expr = None;

        // Parse the rest of the values in the array, or the `; <repeat_count>`, or `]`.
        let end_pos = match Module::parse_expecting_any(
            tokens,
            vec![
                TokenKind::Comma,
                TokenKind::SemiColon,
                TokenKind::RightBracket,
            ],
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
                    vec![TokenKind::Comma, TokenKind::RightBracket],
                ) {
                    Ok(Token {
                        kind: TokenKind::RightBracket,
                        span,
                        ..
                    }) => break span.end_pos,

                    Ok(Token {
                        kind: TokenKind::Comma,
                        span,
                        ..
                    }) => {
                        // Handle the trailing comma.
                        if Module::parse_optional(tokens, TokenKind::RightBracket).is_some() {
                            break span.end_pos;
                        }
                    }

                    Err(err) => return Err(err),

                    _ => unreachable!(),
                }
            },

            Ok(Token {
                kind: TokenKind::RightBracket,
                span,
                ..
            }) => {
                // Nothing to do here. It's the end of the array.
                span.end_pos
            }

            Ok(_) => {
                maybe_repeat_expr = Some(Expression::from(tokens)?);
                Module::parse_expecting(tokens, TokenKind::RightBracket)?
                    .span
                    .end_pos
            }

            Err(err) => return Err(err),
        };

        Ok(ArrayInit {
            values,
            maybe_repeat_expr,
            span: Span { start_pos, end_pos },
        })
    }
}
