use std::fmt;

/// Represents the position (line and column) within a file.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct Position {
    pub line: usize,
    pub col: usize,
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Add one to the line and col numbers before printing, because text editors index from 1.
        write!(f, "[{}:{}]", self.line + 1, self.col + 1)
    }
}

impl Default for Position {
    fn default() -> Self {
        Position { line: 0, col: 0 }
    }
}

impl Position {
    pub fn new(line: usize, col: usize) -> Self {
        Position { line, col }
    }
}

pub trait Locatable {
    fn start_pos(&self) -> &Position;
    fn end_pos(&self) -> &Position;
}

/// Implements the `Locatable` trait for any type that has `start_pos` and `end_pos` fields.
#[macro_export]
macro_rules! locatable_impl {
    ($t:ident) => {
        impl Locatable for $t {
            fn start_pos(&self) -> &Position {
                &self.start_pos
            }

            fn end_pos(&self) -> &Position {
                &self.end_pos
            }
        }
    };
}
