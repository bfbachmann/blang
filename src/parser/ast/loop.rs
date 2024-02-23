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
use crate::parser::source::Source;

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
    ///     for <init>; <cond>; <update>; <body>
    ///     while <cond>; <body>
    ///     loop <body>
    ///
    /// where
    /// - `init` is an initialization statement
    /// - `cond` is the expression representing the loop condition that executes before each iteration
    /// - `update` is the update statement that runs at the end of each iteration
    /// - `body` is a statement representing the loop body.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let token = Source::parse_expecting_any(
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
    let start_pos = Source::current_position(tokens);

    // The first token should be `loop`.
    Source::parse_expecting(tokens, TokenKind::Loop)?;

    // The rest should be the statement or closure representing the loop body.
    let body = Closure::from(tokens)?;

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
    let start_pos = Source::current_position(tokens);

    // The first token should be `while`.
    Source::parse_expecting(tokens, TokenKind::While)?;

    // The next tokens should be the loop condition expression.
    let maybe_cond = Some(Expression::from(tokens)?);

    Source::parse_expecting(tokens, TokenKind::SemiColon)?;

    // The rest should be the statement or closure representing the loop body.
    let body = Closure::from(tokens)?;

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
    let start_pos = Source::current_position(tokens);

    // The first token should be `for`.
    Source::parse_expecting(tokens, TokenKind::For)?;

    // If this is a for loop, parse the init, condition, and update segments before the loop body.
    // Parse the optional initialization statement.
    let maybe_init = if Source::next_token_is(tokens, &TokenKind::SemiColon) {
        None
    } else {
        Some(Statement::from(tokens)?)
    };

    Source::parse_expecting(tokens, TokenKind::SemiColon)?;

    // Parse the optional condition expression.
    let maybe_cond = if Source::next_token_is(tokens, &TokenKind::SemiColon) {
        None
    } else {
        Some(Expression::from(tokens)?)
    };

    Source::parse_expecting(tokens, TokenKind::SemiColon)?;

    // Parse the optional update statement.
    let maybe_update = if Source::next_token_is(tokens, &TokenKind::SemiColon) {
        None
    } else {
        Some(Statement::from(tokens)?)
    };

    Source::parse_expecting(tokens, TokenKind::SemiColon)?;

    // The rest should be the statement representing the loop body.
    let body = Closure::from(tokens)?;

    Ok(Loop {
        maybe_init,
        maybe_cond,
        maybe_update,
        body,
        start_pos,
    })
}
