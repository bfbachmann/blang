use std::collections::{HashSet, VecDeque};

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::closure::Closure;
use crate::parser::program::Program;
use crate::parser::ParseResult;

/// Represents a closure that is executed repeatedly.
#[derive(Debug, PartialEq, Clone)]
pub struct Loop {
    pub closure: Closure,
    start_pos: Position,
}

impl Locatable for Loop {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        self.closure.end_pos()
    }
}

impl Loop {
    /// Creates a new closure.
    pub fn new(closure: Closure, start_pos: Position) -> Self {
        Loop { closure, start_pos }
    }

    /// Parses a loop. Expects token sequences of the form
    ///
    ///     loop { ... }
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // Record the starting position of the loop.
        let start_pos = Program::current_position(tokens);

        // The first token should be "loop".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Loop]))?;

        // The rest should be the closure representing the loop body.
        let body = Closure::from(tokens)?;
        Ok(Loop::new(body, start_pos))
    }
}
