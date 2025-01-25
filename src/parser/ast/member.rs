use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::Span;
use crate::locatable_impl; use crate::Locatable;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::symbol::Symbol;

/// Represents the access of a member on come value. This could be a call or reference to
/// a method on a value or type, or a struct or tuple field access.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct MemberAccess {
    pub base_expr: Expression,
    pub member_symbol: Symbol,
    pub span: Span,
}

locatable_impl!(MemberAccess);

impl Hash for MemberAccess {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.base_expr.hash(state);
        self.member_symbol.hash(state);
    }
}

impl Display for MemberAccess {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.base_expr, self.member_symbol)
    }
}
