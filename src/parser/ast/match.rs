use std::fmt::{Debug, Display, Formatter};

use crate::lexer::pos::Position;
use crate::lexer::pos::Span;
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::closure::Closure;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::statement::Statement;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;
use crate::Locatable;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum PatternKind {
    LetBinding(bool, Expression),
    Expr(Expression),
    Wildcard,
}

locatable_impl!(Pattern);

impl Pattern {
    /// Parses a pattern from the token sequence. Expects token sequences of the forms
    ///
    ///     let [mut] <expr>
    ///     <expr>
    ///     _
    fn from(tokens: &mut Stream<Token>) -> ParseResult<Pattern> {
        // Check for wildcard pattern.
        match tokens.peek_next() {
            Some(Token {
                kind: TokenKind::Identifier(ident),
                span,
            }) if ident == "_" => {
                let span = span.clone();
                tokens.next();
                return Ok(Pattern {
                    kind: PatternKind::Wildcard,
                    span,
                });
            }
            _ => {}
        }

        // Check for `let` pattern.
        if let Some(token) = Module::parse_optional(tokens, TokenKind::Let) {
            let start_pos = token.span.start_pos;
            let is_mut = Module::parse_optional(tokens, TokenKind::Mut).is_some();
            let binding_expr = Expression::from(tokens)?;
            let end_pos = binding_expr.end_pos().clone();
            return Ok(Pattern {
                kind: PatternKind::LetBinding(is_mut, binding_expr),
                span: Span { start_pos, end_pos },
            });
        }

        // Handle arbitrary expression.
        let expr = Expression::from(tokens)?;
        let span = expr.span().clone();
        Ok(Pattern {
            kind: PatternKind::Expr(expr),
            span,
        })
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct MatchCase {
    pub pattern: Pattern,
    pub maybe_cond: Option<Expression>,
    pub body: Closure,
}

impl MatchCase {
    /// Parses a match case from the token stream. Expects token sequences of the forms
    ///
    ///     case <pattern>: <statement>...
    ///     case <pattern> if <cond>: <statement>...
    fn from(tokens: &mut Stream<Token>) -> ParseResult<MatchCase> {
        let case_token = Module::parse_expecting(tokens, TokenKind::Case)?;

        let (pattern, maybe_cond) = if Module::parse_optional(tokens, TokenKind::Colon).is_some() {
            // Default (empty) case.
            (
                Pattern {
                    kind: PatternKind::Wildcard,
                    span: case_token.span,
                },
                None,
            )
        } else {
            // Case with pattern and optional condition.
            let pattern = Pattern::from(tokens)?;
            let maybe_cond = match Module::parse_optional(tokens, TokenKind::If) {
                Some(_) => Some(Expression::from(tokens)?),
                None => None,
            };

            Module::parse_expecting(tokens, TokenKind::Colon)?;

            (pattern, maybe_cond)
        };

        let body_start = Module::current_position(tokens);

        let mut statements = vec![];
        while !Module::next_token_is_one_of(tokens, &vec![TokenKind::Case, TokenKind::RightBrace]) {
            statements.push(Statement::from(tokens)?);
        }

        let body = Closure::new(
            statements,
            Span {
                start_pos: body_start,
                end_pos: Module::current_position(tokens),
            },
        );

        Ok(MatchCase {
            pattern,
            maybe_cond,
            body,
        })
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Match {
    pub target: Expression,
    pub cases: Vec<MatchCase>,
    pub span: Span,
}

impl Display for Match {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "match {{ ... }}")
    }
}

locatable_impl!(Match);

impl Match {
    /// Parses a match statement from the token stream. Expects token sequences of the form:
    ///
    ///     match <target> {
    ///         <match_case>
    ///         ...
    ///     }
    ///
    /// where
    /// - `target` is the match target expression
    /// - `match_case` is a match case (see `MatchCase::from`)
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Match> {
        let start_pos = Module::parse_expecting(tokens, TokenKind::Match)?
            .span
            .start_pos;

        let target = Expression::from(tokens)?;

        Module::parse_expecting(tokens, TokenKind::LeftBrace)?;

        let mut cases = vec![];
        let end_pos = loop {
            if let Some(token) = Module::parse_optional(tokens, TokenKind::RightBrace) {
                break token.span.end_pos;
            }

            cases.push(MatchCase::from(tokens)?);
        };

        Ok(Match {
            target,
            cases,
            span: Span { start_pos, end_pos },
        })
    }
}
