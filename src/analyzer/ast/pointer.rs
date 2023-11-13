use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::parser::pointer::PointerType;
use std::fmt::{Display, Formatter};

/// Represents a pointer to some known type.
#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct APointerType {
    pub pointee_type_key: TypeKey,
}

impl Display for APointerType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "*{}", self.pointee_type_key)
    }
}

impl APointerType {
    /// Creates a new pointer type with the given pointee type.
    pub fn new(pointee_type_key: TypeKey) -> APointerType {
        APointerType { pointee_type_key }
    }

    /// Performs semantic analysis on the given pointer type.
    pub fn from(ctx: &mut ProgramContext, typ: &PointerType) -> APointerType {
        let pointee_type_key = ctx.resolve_type(&typ.pointee_type);
        APointerType { pointee_type_key }
    }

    /// Returns the human-readable version of this pointer type.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        format!("*{}", ctx.must_get_type(self.pointee_type_key)).to_string()
    }
}
