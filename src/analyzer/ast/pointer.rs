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

    /// Returns true if this pointer type is the compatible with `other`.
    pub fn is_same_as(
        &self,
        ctx: &ProgramContext,
        other: &APointerType,
        ignore_mutability: bool,
    ) -> bool {
        let same_pointee_types =
            ctx.types_match(self.pointee_type_key, other.pointee_type_key, false);
        same_pointee_types && (ignore_mutability || self.is_mut == other.is_mut)
    }

    /// Returns the human-readable version of this pointer type.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        format!(
            "*{}{}",
            match self.is_mut {
                true => "mut ",
                false => "",
            },
            ctx.display_type(self.pointee_type_key)
        )
        .to_string()
    }
}
