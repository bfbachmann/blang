use std::fmt::{Display, Formatter};

use crate::lexer::pos::Span;
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::symbol::Symbol;
use crate::Locatable;

/// Represents the access of a member on come value. This could be a call or reference to
/// a method on a value or type, or a struct or tuple field access.
#[derive(Debug, PartialEq, Clone)]
pub struct MemberAccess {
    pub base_expr: Expression,
    pub member_symbol: Symbol,
    pub span: Span,
}

locatable_impl!(MemberAccess);

impl Display for MemberAccess {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.base_expr, self.member_symbol)
    }
}
