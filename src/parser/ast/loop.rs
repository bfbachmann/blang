use crate::lexer::pos::Span;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::closure::Closure;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::statement::Statement;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a closure that is executed repeatedly.
#[derive(Debug, PartialEq, Clone)]
pub struct Loop {
    pub maybe_init: Option<Statement>,
    pub maybe_cond: Option<Expression>,
    pub maybe_update: Option<Statement>,
    pub body: Closure,
    pub span: Span,
}

locatable_impl!(Loop);

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
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        let token =
            parser.parse_expecting_any(vec![TokenKind::Loop, TokenKind::While, TokenKind::For])?;
        parser.tokens.rewind(1);

        match &token.kind {
            TokenKind::Loop => parse_loop(parser),
            TokenKind::While => parse_while(parser),
            TokenKind::For => parse_for(parser),
            _ => unreachable!(),
        }
    }
}

/// Parses a `loop` loop.
fn parse_loop(parser: &mut FileParser) -> ParseResult<Loop> {
    // Record the starting position of the loop.
    let start_pos = parser.current_position();

    // The first token should be `loop`.
    parser.parse_expecting(TokenKind::Loop)?;

    let body = Closure::parse(parser)?;

    Ok(Loop {
        maybe_init: None,
        maybe_cond: None,
        maybe_update: None,
        span: parser.new_span(start_pos, body.span().end_pos),
        body,
    })
}

/// Parse a `while` loop.
fn parse_while(parser: &mut FileParser) -> ParseResult<Loop> {
    // Record the starting position of the loop.
    let start_pos = parser.current_position();

    // The first token should be `while`.
    parser.parse_expecting(TokenKind::While)?;

    // The next tokens should be the loop condition expression.
    let maybe_cond = Some(Expression::parse(parser)?);

    let body = Closure::parse(parser)?;

    Ok(Loop {
        maybe_init: None,
        maybe_cond,
        maybe_update: None,
        span: parser.new_span(start_pos, body.span().end_pos),
        body,
    })
}

/// Parses a `for` loop.
fn parse_for(parser: &mut FileParser) -> ParseResult<Loop> {
    // Record the starting position of the loop.
    let start_pos = parser.current_position();

    // The first token should be `for`.
    parser.parse_expecting(TokenKind::For)?;

    // If this is a for loop, parse the init, condition, and update segments before the loop body.
    // Parse the optional initialization statement.
    let maybe_init = if parser.next_token_is(&TokenKind::SemiColon) {
        None
    } else {
        Some(Statement::parse(parser)?)
    };

    parser.parse_expecting(TokenKind::SemiColon)?;

    // Parse the optional condition expression.
    let maybe_cond = if parser.next_token_is(&TokenKind::SemiColon) {
        None
    } else {
        Some(Expression::parse(parser)?)
    };

    parser.parse_expecting(TokenKind::SemiColon)?;

    // Parse the optional update statement.
    let maybe_update = if parser.next_token_is(&TokenKind::SemiColon) {
        None
    } else {
        Some(Statement::parse(parser)?)
    };

    let body = Closure::parse(parser)?;

    Ok(Loop {
        maybe_init,
        maybe_cond,
        maybe_update,
        span: parser.new_span(start_pos, body.span().end_pos),
        body,
    })
}
