use crate::lexer::pos::Span;

pub type LexResult<T> = Result<T, LexError>;

/// Represents any fatal error that occurs during lexing.
#[derive(Debug, PartialEq)]
pub struct LexError {
    pub message: String,
    pub span: Span,
}
