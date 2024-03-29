use crate::lexer::pos::Position;

pub type LexResult<T> = Result<T, LexError>;

/// Represents any fatal error that occurs during lexing.
#[derive(Debug, PartialEq)]
pub struct LexError {
    pub message: String,
    pub start_pos: Position,
    pub end_pos: Position,
}
