use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::r#type::Type;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

/// Represents a lambda function argument declaration. Lambda arguments may or may not have defined
/// types. Arguments without types will be treated as generic arguments.
#[derive(Debug, Clone, PartialEq)]
pub struct LambdaArg {
    pub name: String,
    pub maybe_type: Option<Type>,
    pub is_mut: bool,
    span: Span,
}

locatable_impl!(LambdaArg);

/// Represents a lambda function declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct LambdaDecl {
    pub args: Vec<LambdaArg>,
    pub expr: Expression,
    span: Span,
}

locatable_impl!(LambdaDecl);

impl LambdaDecl {
    /// Parses a lambda function declaration from the token sequence. Expects token sequences of
    /// the form
    ///
    ///     $(<arg_name>: <arg_type>, ...) <expr>
    ///
    /// where
    /// - `arg_name` is an identifier representing an argument name
    /// - `arg_type` is the optional argument type (see `Type::from`)
    /// - `expr` is the expression returned by the lambda function (see `Expression::from`).
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let start_pos = Module::parse_expecting(tokens, TokenKind::DollarSign)?
            .span
            .start_pos;
        Module::parse_expecting(tokens, TokenKind::LeftParen)?;

        // Parse lambda arguments.
        let mut args: Vec<LambdaArg> = vec![];
        while !Module::next_token_is(tokens, &TokenKind::RightParen) {
            let start_pos = Module::current_position(tokens);
            let is_mut = Module::parse_optional(tokens, TokenKind::Mut).is_some();
            let name = Module::parse_identifier(tokens)?;
            let maybe_type = match Module::parse_optional(tokens, TokenKind::Colon) {
                Some(_) => Some(Type::from(tokens)?),
                None => None,
            };

            args.push(LambdaArg {
                name,
                maybe_type,
                is_mut,
                span: Span {
                    start_pos,
                    end_pos: Module::prev_position(tokens),
                },
            });

            // The next token should either be `,` or `)`.
            let next_token =
                Module::parse_expecting_any(tokens, vec![TokenKind::Comma, TokenKind::RightParen])?;
            match next_token.kind {
                TokenKind::RightParen => break,
                _ => {}
            };
        }

        // Parse lambda expression.
        let expr = Expression::from(tokens)?;
        let end_pos = expr.end_pos().clone();

        Ok(LambdaDecl {
            args,
            expr,
            span: Span { start_pos, end_pos },
        })
    }
}
