use std::fmt::{Debug, Display, Formatter};

use crate::lexer::pos::Position;
use crate::lexer::pos::Span;
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::closure::Closure;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::r#enum::EnumVariantInit;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;
use crate::Locatable;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum PatternKind {
    LetEnumVariant(bool, EnumVariantInit),
    Expr(Expression),
    Wildcard,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

locatable_impl!(Pattern);

impl Pattern {
    /// Parses a pattern from the token sequence. Expects token sequences of the forms
    ///
    ///     let <enum_type>::<variant>(<expr>)
    ///     let mut <enum_type>::<variant>(<expr>)
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
            let enum_pattern = EnumVariantInit::from(tokens)?;
            let end_pos = enum_pattern.end_pos().clone();
            return Ok(Pattern {
                kind: PatternKind::LetEnumVariant(is_mut, enum_pattern),
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
    ///     <pattern> <closure>
    ///     <pattern> if <cond> <closure>
    fn from(tokens: &mut Stream<Token>) -> ParseResult<MatchCase> {
        let pattern = Pattern::from(tokens)?;
        let maybe_cond = match Module::parse_optional(tokens, TokenKind::If) {
            Some(_) => Some(Expression::from(tokens)?),
            None => None,
        };
        let body = Closure::from(tokens)?;
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
