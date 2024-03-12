use std::collections::HashSet;
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
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
    start_pos: Position,
}

impl Hash for Loop {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.body.hash(state);
    }
}

impl Locatable for Loop {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        self.body.end_pos()
    }
}

impl Loop {
    /// Parses a loop. Expects token sequences of the form
    ///
    ///     for <init>, <cond>, <update>: <statement>
    ///     for <init>, <cond>, <update> <closure>
    ///     while <cond>: <statement>
    ///     while <cond> <closure>
    ///     loop: <statement>
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
            HashSet::from([TokenKind::Loop, TokenKind::While, TokenKind::For]),
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

    // The next tokens should either be `: <statement>` or just a closure.
    let body = if Module::parse_optional(tokens, TokenKind::Colon).is_some() {
        let statement = Statement::from(tokens)?;
        let start_pos = statement.start_pos().clone();
        let end_pos = statement.end_pos().clone();
        Closure::new(vec![statement], None, start_pos, end_pos)
    } else {
        Closure::from(tokens)?
    };

    Ok(Loop {
        maybe_init: None,
        maybe_cond: None,
        maybe_update: None,
        body,
        start_pos,
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

    // The next tokens should either be `: <statement>` or just a closure.
    let body = if Module::parse_optional(tokens, TokenKind::Colon).is_some() {
        let statement = Statement::from(tokens)?;
        let start_pos = statement.start_pos().clone();
        let end_pos = statement.end_pos().clone();
        Closure::new(vec![statement], None, start_pos, end_pos)
    } else {
        Closure::from(tokens)?
    };

    Ok(Loop {
        maybe_init: None,
        maybe_cond,
        maybe_update: None,
        body,
        start_pos,
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
    let maybe_init = if Module::next_token_is(tokens, &TokenKind::Comma) {
        None
    } else {
        Some(Statement::from(tokens)?)
    };

    Module::parse_expecting(tokens, TokenKind::Comma)?;

    // Parse the optional condition expression.
    let maybe_cond = if Module::next_token_is(tokens, &TokenKind::Comma) {
        None
    } else {
        Some(Expression::from(tokens)?)
    };

    Module::parse_expecting(tokens, TokenKind::Comma)?;

    // Parse the optional update statement.
    let maybe_update = if Module::next_token_is(tokens, &TokenKind::Comma) {
        None
    } else {
        Some(Statement::from(tokens)?)
    };

    // The next tokens should either be `: <statement>` or just a closure.
    let body = if Module::parse_optional(tokens, TokenKind::Colon).is_some() {
        let statement = Statement::from(tokens)?;
        let start_pos = statement.start_pos().clone();
        let end_pos = statement.end_pos().clone();
        Closure::new(vec![statement], None, start_pos, end_pos)
    } else {
        Closure::from(tokens)?
    };

    Ok(Loop {
        maybe_init,
        maybe_cond,
        maybe_update,
        body,
        start_pos,
    })
}
