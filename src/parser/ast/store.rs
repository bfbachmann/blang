use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;

/// A store statement that writes a value to memory.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Store {
    pub dest_expr: Expression,
    pub source_expr: Expression,
    start_pos: Position,
    end_pos: Position,
}

impl Hash for Store {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.dest_expr.hash(state);
        self.source_expr.hash(state);
    }
}

locatable_impl!(Store);

impl Store {
    /// Creates a new store statement.
    pub fn new(dest: Expression, source: Expression) -> Store {
        Store {
            start_pos: dest.start_pos().clone(),
            end_pos: source.end_pos().clone(),
            dest_expr: dest,
            source_expr: source,
        }
    }
}
