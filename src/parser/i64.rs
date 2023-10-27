use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::locatable_impl;

/// Represents a 64 bit signed integer type.
#[derive(Debug, Clone, Eq, Default)]
pub struct I64Type {
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for I64Type {
    fn eq(&self, _other: &Self) -> bool {
        // Two i64 types are always considered equal.
        true
    }
}

impl Hash for I64Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "i64".hash(state);
    }
}

locatable_impl!(I64Type);

impl I64Type {
    pub fn new(start_pos: Position, end_pos: Position) -> Self {
        I64Type { start_pos, end_pos }
    }
}
