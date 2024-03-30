use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;

#[derive(Eq, Debug, Clone)]
pub struct Index {
    pub collection_expr: Expression,
    pub index_expr: Expression,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(Index);

impl Display for Index {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.({})", self.collection_expr, self.index_expr)
    }
}

impl Hash for Index {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.collection_expr.hash(state);
        self.index_expr.hash(state);
    }
}

impl PartialEq for Index {
    fn eq(&self, other: &Self) -> bool {
        self.collection_expr == other.collection_expr && self.index_expr == other.index_expr
    }
}

impl Index {
    pub fn new(collection_expr: Expression, index_expr: Expression) -> Index {
        Index {
            start_pos: collection_expr.start_pos().clone(),
            end_pos: collection_expr.end_pos().clone(),
            collection_expr,
            index_expr,
        }
    }
}
