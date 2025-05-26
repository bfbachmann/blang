use std::fmt::{Debug, Display, Formatter};

use crate::lexer::pos::Span;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::closure::Closure;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::statement::Statement;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;

#[derive(Debug, PartialEq, Clone)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

#[derive(Debug, PartialEq, Clone)]
pub enum PatternKind {
    LetBinding(bool, Vec<Expression>),
    Exprs(Vec<Expression>),
    Wildcard,
}

locatable_impl!(Pattern);

impl Pattern {
    /// Parses a pattern from the token sequence. Expects token sequences of the forms
    ///
    ///     let [mut] <expr>
    ///     <expr>
    ///     _
    ///     <empty>
    fn parse(parser: &mut FileParser) -> ParseResult<Pattern> {
        // Handle empty pattern.
        if parser.next_token_is_one_of(&vec![TokenKind::Colon, TokenKind::If]) {
            let prev_token = parser.tokens.prev().unwrap();
            return Ok(Pattern {
                kind: PatternKind::Wildcard,
                span: prev_token.span,
            });
        }

        // Check for wildcard pattern.
        match parser.tokens.peek_next() {
            Some(Token {
                kind: TokenKind::Identifier(ident),
                span,
            }) if ident == "_" => {
                let span = *span;
                parser.tokens.next();
                return Ok(Pattern {
                    kind: PatternKind::Wildcard,
                    span,
                });
            }
            _ => {}
        }

        // Check for `let` pattern.
        if let Some(token) = parser.parse_optional(TokenKind::Let) {
            let start_pos = token.span.start_pos;
            let is_mut = parser.parse_optional(TokenKind::Mut).is_some();

            let mut exprs = vec![Expression::parse(parser)?];
            while parser.parse_optional(TokenKind::Comma).is_some() {
                exprs.push(Expression::parse(parser)?);
            }

            let end_pos = exprs.last().unwrap().span().end_pos;

            return Ok(Pattern {
                kind: PatternKind::LetBinding(is_mut, exprs),
                span: parser.new_span(start_pos, end_pos),
            });
        }

        // Handle arbitrary expressions.
        let mut exprs = vec![Expression::parse(parser)?];
        while parser.parse_optional(TokenKind::Comma).is_some() {
            exprs.push(Expression::parse(parser)?);
        }

        Ok(Pattern {
            span: parser.new_span(
                exprs.first().unwrap().span().start_pos,
                exprs.last().unwrap().span().end_pos,
            ),
            kind: PatternKind::Exprs(exprs),
        })
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct MatchCase {
    pub pattern: Pattern,
    pub maybe_cond: Option<Expression>,
    pub body: Closure,
    pub span: Span,
}

impl MatchCase {
    /// Parses a match case from the token stream. Expects token sequences of the forms
    ///
    ///     <patter> => <statement>
    ///     <pattern> if <cond> => <statement>
    fn parse(parser: &mut FileParser) -> ParseResult<MatchCase> {
        let pattern = Pattern::parse(parser)?;
        let maybe_cond = match parser.parse_optional(TokenKind::If) {
            Some(_) => Some(Expression::parse(parser)?),
            None => None,
        };

        parser.parse_expecting(TokenKind::FatArrow)?;

        let body = match Statement::parse(parser)? {
            Statement::Closure(closure) => closure,
            statement => {
                let span = *statement.span();
                Closure::new(vec![statement], span)
            }
        };

        Ok(MatchCase {
            span: parser.new_span(pattern.span.start_pos, body.span().end_pos),
            pattern,
            maybe_cond,
            body,
        })
    }
}

#[derive(Debug, PartialEq, Clone)]
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
    /// - `match_case` is a match case
    pub fn parse(parser: &mut FileParser) -> ParseResult<Match> {
        let start_pos = parser.parse_expecting(TokenKind::Match)?.span.start_pos;

        let target = Expression::parse(parser)?;

        parser.parse_expecting(TokenKind::LeftBrace)?;

        let mut cases = vec![];
        let end_pos = loop {
            if let Some(token) = parser.parse_optional(TokenKind::RightBrace) {
                break token.span.end_pos;
            }

            cases.push(MatchCase::parse(parser)?);
        };

        Ok(Match {
            target,
            cases,
            span: Span {
                file_id: parser.file_id,
                start_pos,
                end_pos,
            },
        })
    }
}
