use std::collections::{HashSet, VecDeque};

use crate::lexer::kind::TokenKind;
use crate::lexer::token::Token;
use crate::parser::closure::Closure;
use crate::parser::program::Program;
use crate::parser::ParseResult;

/// Represents a closure that is executed repeatedly.
#[derive(Debug, PartialEq, Clone)]
pub struct Loop {
    pub closure: Closure,
}

impl Loop {
    pub fn new(closure: Closure) -> Self {
        Loop { closure }
    }

    /// Parses a loop. Expects token sequences of the form
    ///
    ///     loop { ... }
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token should be "loop".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Loop]))?;

        // The rest should be the closure representing the loop body.
        let body = Closure::from(tokens)?;
        Ok(Loop::new(body))
    }
}
