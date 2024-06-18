use std::fmt::{Display, Formatter};

use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::parser::ast::pointer::PointerType;

/// Represents a pointer to some known type.
#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct APointerType {
    pub pointee_type_key: TypeKey,
    /// Indicates whether the pointee can be modified via this pointer.
    pub is_mut: bool,
}

impl Display for APointerType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "*{}{}",
            match self.is_mut {
                true => "mut ",
                false => "",
            },
            self.pointee_type_key
        )
    }
}

impl APointerType {
    /// Creates a new pointer type with the given pointee type.
    pub fn new(pointee_type_key: TypeKey, is_mut: bool) -> APointerType {
        APointerType {
            pointee_type_key,
            is_mut,
        }
    }

    /// Performs semantic analysis on the given pointer type.
    pub fn from(ctx: &mut ProgramContext, typ: &PointerType) -> APointerType {
        let pointee_type_key = ctx.resolve_type(&typ.pointee_type);
        APointerType {
            pointee_type_key,
            is_mut: typ.is_mut,
        }
    }

    /// Returns the human-readable version of this pointer type.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        format!(
            "*{}{}",
            match self.is_mut {
                true => "mut ",
                false => "",
            },
            ctx.must_get_type(self.pointee_type_key).display(ctx)
        )
        .to_string()
    }
}
