use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::locatable_impl;

/// Represents a static type (i.e. a string literal that is allocated globally).
#[derive(Debug, Clone, Eq)]
pub struct StrType {
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for StrType {
    fn eq(&self, _other: &Self) -> bool {
        // Two str types are always considered equal.
        true
    }
}

impl Hash for StrType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "str".hash(state);
    }
}

locatable_impl!(StrType);

impl StrType {
    pub fn new(start_pos: Position, end_pos: Position) -> Self {
        StrType { start_pos, end_pos }
    }

    pub fn default() -> Self {
        StrType {
            start_pos: Default::default(),
            end_pos: Default::default(),
        }
    }
}
