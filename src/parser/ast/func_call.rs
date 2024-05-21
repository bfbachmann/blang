use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;

/// Represents a function call.
#[derive(Eq, Debug, Clone)]
pub struct FuncCall {
    pub fn_expr: Expression,
    pub args: Vec<Expression>,
    pub(crate) span: Span,
}

locatable_impl!(FuncCall);

impl Display for FuncCall {
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

impl Hash for FuncCall {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.fn_expr.hash(state);
        for arg in &self.args {
            arg.hash(state);
        }
    }
}

impl PartialEq for FuncCall {
    fn eq(&self, other: &Self) -> bool {
        self.fn_expr == other.fn_expr && self.args == other.args
    }
}

impl FuncCall {
    pub fn new(fn_expr: Expression, args: Vec<Expression>, end_pos: Position) -> FuncCall {
        FuncCall {
            span: Span {
                start_pos: fn_expr.start_pos().clone(),
                end_pos,
            },
            fn_expr,
            args,
        }
    }

    #[cfg(test)]
    pub fn new_with_default_pos(fn_expr: Expression, args: Vec<Expression>) -> FuncCall {
        FuncCall {
            fn_expr,
            args,
            span: Default::default(),
        }
    }
}
