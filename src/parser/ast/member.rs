use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;

/// Represents the access of a member on come value. This could be a call or reference to
/// a method on a value or type, or a struct or tuple field access.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct MemberAccess {
    pub expr: Expression,
    pub member_name: String,
    span: Span,
}

locatable_impl!(MemberAccess);

impl Hash for MemberAccess {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.expr.hash(state);
        self.member_name.hash(state);
    }
}

impl Display for MemberAccess {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.expr, self.member_name)
    }
}

impl MemberAccess {
    /// Creates a new member access expression.
    pub fn new(expr: Expression, member_name: String, span: Span) -> MemberAccess {
        MemberAccess {
            expr,
            member_name,
            span,
        }
    }
}
