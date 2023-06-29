use std::fmt;

/// Represents the position (line and column) within a file.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Position {
    line: usize,
    col: usize,
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[{}:{}]", self.line, self.col)
    }
}

impl Position {
    pub fn new(line: usize, col: usize) -> Self {
        Position { line, col }
    }
}
