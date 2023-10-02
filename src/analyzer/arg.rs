use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::parser::arg::Argument;

/// Represents a semantically valid function argument.
#[derive(PartialEq, Debug, Clone)]
pub struct RichArg {
    pub name: String,
    pub type_id: TypeId,
    pub is_mut: bool,
}

impl fmt::Display for RichArg {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.name.is_empty() {
            write!(f, "{}", self.type_id)
        } else {
            write!(f, "{}: {}", self.name, self.type_id)
        }
    }
}

impl RichArg {
    /// Performs semantic analysis on the argument and returns an analyzed version of it.
    pub fn from(ctx: &mut ProgramContext, arg: &Argument) -> Self {
        RichArg {
            name: arg.name.to_string(),
            type_id: RichType::analyze(ctx, &arg.typ),
            is_mut: arg.is_mut,
        }
    }
}
