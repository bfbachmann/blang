use std::fmt::{Display, Formatter};

use crate::lexer::pos::Span;
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;
use crate::Locatable;

#[derive(Debug, Clone)]
pub struct Index {
    pub collection_expr: Expression,
    pub index_expr: Expression,
    pub span: Span,
}

locatable_impl!(Index);

impl Display for Index {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.({})", self.collection_expr, self.index_expr)
    }
}

impl PartialEq for Index {
    fn eq(&self, other: &Self) -> bool {
        self.collection_expr == other.collection_expr && self.index_expr == other.index_expr
    }
}
