use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::locatable_impl;

/// Represents a raw pointer that is not automatically garbage collected and allows pointer
/// arithmetic. This type translates directly to `void *` in C.
#[derive(Debug, Clone, Eq)]
pub struct UnsafePtrType {
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for UnsafePtrType {
    fn eq(&self, _other: &Self) -> bool {
        // Two unsafeptr types are always considered equal.
        true
    }
}

impl Hash for UnsafePtrType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "unsafeptr".hash(state);
    }
}

locatable_impl!(UnsafePtrType);

impl UnsafePtrType {
    pub fn new(start_pos: Position, end_pos: Position) -> Self {
        UnsafePtrType { start_pos, end_pos }
    }

    pub fn default() -> Self {
        UnsafePtrType {
            start_pos: Default::default(),
            end_pos: Default::default(),
        }
    }
}
