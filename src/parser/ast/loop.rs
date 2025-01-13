use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::closure::Closure;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::statement::Statement;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

/// Represents a closure that is executed repeatedly.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Loop {
    pub maybe_init: Option<Statement>,
    pub maybe_cond: Option<Expression>,
    pub maybe_update: Option<Statement>,
    pub body: Closure,
    pub span: Span,
}

locatable_impl!(Loop);

impl Hash for Loop {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.body.hash(state);
    }
}

impl Loop {
    /// Parses a loop. Expects token sequences of the form
    ///
    ///     for <init>; <cond>; <update> <closure>
    ///     while <cond> <closure>
    ///     loop <closure>
    ///
    /// where
    /// - `init` is an initialization statement
    /// - `cond` is the expression representing the loop condition that executes before each iteration
    /// - `update` is the update statement that runs at the end of each iteration
    /// - `statement` is a statement representing the loop body
    /// - `closure` is a closure representing the loop body.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let token = Module::parse_expecting_any(
            tokens,
            vec![TokenKind::Loop, TokenKind::While, TokenKind::For],
        )?;
        tokens.rewind(1);

        match &token.kind {
            TokenKind::Loop => parse_loop(tokens),
            TokenKind::While => parse_while(tokens),
            TokenKind::For => parse_for(tokens),
            _ => unreachable!(),
        }
    }
}

/// Parses a `loop` loop.
fn parse_loop(tokens: &mut Stream<Token>) -> ParseResult<Loop> {
    // Record the starting position of the loop.
    let start_pos = Module::current_position(tokens);

    // The first token should be `loop`.
    Module::parse_expecting(tokens, TokenKind::Loop)?;

    let body = Closure::from(tokens)?;

    Ok(Loop {
        maybe_init: None,
        maybe_cond: None,
        maybe_update: None,
        span: Span {
            start_pos,
            end_pos: body.end_pos().clone(),
        },
        body,
    })
}

/// Parse a `while` loop.
fn parse_while(tokens: &mut Stream<Token>) -> ParseResult<Loop> {
    // Record the starting position of the loop.
    let start_pos = Module::current_position(tokens);

    // The first token should be `while`.
    Module::parse_expecting(tokens, TokenKind::While)?;

    // The next tokens should be the loop condition expression.
    let maybe_cond = Some(Expression::from(tokens)?);

    let body = Closure::from(tokens)?;

    Ok(Loop {
        maybe_init: None,
        maybe_cond,
        maybe_update: None,
        span: Span {
            start_pos,
            end_pos: body.end_pos().clone(),
        },
        body,
    })
}

/// Parses a `for` loop.
fn parse_for(tokens: &mut Stream<Token>) -> ParseResult<Loop> {
    // Record the starting position of the loop.
    let start_pos = Module::current_position(tokens);

    // The first token should be `for`.
    Module::parse_expecting(tokens, TokenKind::For)?;

    // If this is a for loop, parse the init, condition, and update segments before the loop body.
    // Parse the optional initialization statement.
    let maybe_init = if Module::next_token_is(tokens, &TokenKind::SemiColon) {
        None
    } else {
        Some(Statement::from(tokens)?)
    };

    Module::parse_expecting(tokens, TokenKind::SemiColon)?;

    // Parse the optional condition expression.
    let maybe_cond = if Module::next_token_is(tokens, &TokenKind::SemiColon) {
        None
    } else {
        Some(Expression::from(tokens)?)
    };

    Module::parse_expecting(tokens, TokenKind::SemiColon)?;

    // Parse the optional update statement.
    let maybe_update = if Module::next_token_is(tokens, &TokenKind::SemiColon) {
        None
    } else {
        Some(Statement::from(tokens)?)
    };

    let body = Closure::from(tokens)?;

    Ok(Loop {
        maybe_init,
        maybe_cond,
        maybe_update,
        span: Span {
            start_pos,
            end_pos: body.end_pos().clone(),
        },
        body,
    })
}
