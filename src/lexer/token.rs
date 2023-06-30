use crate::lexer::Token;

impl Clone for Token {
    fn clone(&self) -> Self {
        Token {
            kind: self.kind.clone(),
            start: self.start,
            end: self.end,
        }
    }
}
