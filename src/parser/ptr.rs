use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::locatable_impl;

/// Represents a raw pointer that is not automatically garbage collected and allows pointer
/// arithmetic. This type translates directly to `void *` in C.
#[derive(Debug, Clone, Eq)]
pub struct PtrType {
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for PtrType {
    fn eq(&self, _other: &Self) -> bool {
        // Two ptr types are always considered equal.
        true
    }
}

impl Hash for PtrType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "ptr".hash(state);
    }
}

locatable_impl!(PtrType);

impl PtrType {
    pub fn new(start_pos: Position, end_pos: Position) -> Self {
        PtrType { start_pos, end_pos }
    }

    pub fn default() -> Self {
        PtrType {
            start_pos: Default::default(),
            end_pos: Default::default(),
        }
    }
}
