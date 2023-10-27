use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::locatable_impl;

/// Represents a pointer-sized unsigned integer.
#[derive(Debug, Clone, Eq, Default)]
pub struct U64Type {
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for U64Type {
    fn eq(&self, _other: &Self) -> bool {
        // Two u64 types are always considered equal.
        true
    }
}

impl Hash for U64Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "u64".hash(state);
    }
}

locatable_impl!(U64Type);

impl U64Type {
    pub fn new(start_pos: Position, end_pos: Position) -> Self {
        U64Type { start_pos, end_pos }
    }
}
