use crate::lexer::pos::Position;

pub type LexResult<T> = Result<T, LexError>;

/// Represents any fatal error that occurs during lexing.
#[derive(Debug, PartialEq)]
pub struct LexError {
    pub message: String,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl LexError {
    pub fn new(message: &str, line: usize, start_col: usize, end_col: usize) -> Self {
        LexError {
            message: message.to_string(),
            start_pos: Position::new(line, start_col),
            end_pos: Position::new(line, end_col),
        }
    }
}
