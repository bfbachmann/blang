use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::closure::Closure;
use crate::parser::error::ParseResult;
use crate::parser::source::Source;

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
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Record the starting position of the loop.
        let start_pos = Source::current_position(tokens);

        // The first token should be `loop`.
        Source::parse_expecting(tokens, TokenKind::Loop)?;

        // The rest should be the closure representing the loop body.
        let body = Closure::from(tokens)?;
        Ok(Loop::new(body, start_pos))
    }
}
