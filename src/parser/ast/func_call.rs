use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Position, Span};
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;
use crate::Locatable;

/// Represents a function call.
#[derive(Eq, Debug, Clone)]
pub struct FnCall {
    pub fn_expr: Expression,
    pub args: Vec<Expression>,
    pub span: Span,
}

locatable_impl!(FnCall);

impl Display for FnCall {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}(", self.fn_expr)?;

        for (i, arg) in self.args.iter().enumerate() {
            match i {
                0 => write!(f, "{}", arg)?,
                _ => write!(f, ", {}", arg)?,
            };
        }

        write!(f, ")")
    }
}

impl Hash for FnCall {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.fn_expr.hash(state);
        for arg in &self.args {
            arg.hash(state);
        }
    }
}

impl PartialEq for FnCall {
    fn eq(&self, other: &Self) -> bool {
        self.fn_expr == other.fn_expr && self.args == other.args
    }
}

impl FnCall {
    pub fn new(fn_expr: Expression, args: Vec<Expression>, end_pos: Position) -> FnCall {
        let span = fn_expr.span();

        FnCall {
            span: Span {
                file_id: span.file_id,
                start_pos: span.start_pos,
                end_pos,
            },
            fn_expr,
            args,
        }
    }

    #[cfg(test)]
    pub fn new_with_default_pos(fn_expr: Expression, args: Vec<Expression>) -> FnCall {
        FnCall {
            fn_expr,
            args,
            span: Default::default(),
        }
    }
}
