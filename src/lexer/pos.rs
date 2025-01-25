use crate::parser::FileID;
use std::fmt;

/// Represents the position (line and column) within a file.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct Position {
    pub line: u32,
    pub col: u32,
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

impl Default for Position {
    fn default() -> Self {
        Position { line: 0, col: 0 }
    }
}

impl Position {
    pub fn new(line: u32, col: u32) -> Self {
        Position { line, col }
    }
}

pub trait Locatable {
    fn span(&self) -> &Span;
}

/// Implements the `Locatable` trait for any type that has a `span` field.
#[macro_export]
macro_rules! locatable_impl {
    ($t:ident) => {
        impl Locatable for $t {
            fn span(&self) -> &Span {
                &self.span
            }
        }
    };
}

/// Represents a fragment of code in a file.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash, Default)]
pub struct Span {
    pub file_id: FileID,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Locatable for Span {
    fn span(&self) -> &Span {
        self
    }
}
