use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::parser::arg::Argument;

/// Represents a semantically valid function argument.
#[derive(PartialEq, Debug, Clone)]
pub struct AArg {
    pub name: String,
    pub type_key: TypeKey,
    pub is_mut: bool,
}

impl fmt::Display for AArg {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.name.is_empty() {
            write!(f, "{}", self.type_key)
        } else {
            write!(f, "{}: {}", self.name, self.type_key)
        }
    }
}

impl AArg {
    /// Performs semantic analysis on the argument and returns an analyzed version of it.
    pub fn from(ctx: &mut ProgramContext, arg: &Argument) -> Self {
        AArg {
            name: arg.name.to_string(),
            type_key: ctx.resolve_type(&arg.typ),
            is_mut: arg.is_mut,
        }
    }

    /// Returns a string containing a human-readable version of the argument.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let type_display = ctx.display_type_for_key(self.type_key);
        match self.name.is_empty() {
            true => format!("{}", type_display).to_string(),
            false => format!("{}: {}", self.name, type_display).to_string(),
        }
    }
}
