use std::collections::HashMap;
use std::fmt::{Display, Formatter};

use crate::analyzer::ast::r#type::AType;
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

    /// Converts this pointer type from a polymorphic (parameterized) type into a
    /// monomorph by substituting type keys for generic types with those from the
    /// provided parameter values.
    pub fn monomorphize(
        &mut self,
        ctx: &mut ProgramContext,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) -> Option<TypeKey> {
        if let Some(replacement_tk) = type_mappings.get(&self.pointee_type_key) {
            self.pointee_type_key = *replacement_tk;
            return Some(ctx.insert_type(AType::Pointer(self.clone())));
        }

        let pointee_type = ctx.must_get_type(self.pointee_type_key);
        if let Some(replacement_tk) = pointee_type.clone().monomorphize(ctx, type_mappings) {
            self.pointee_type_key = replacement_tk;
            return Some(ctx.insert_type(AType::Pointer(self.clone())));
        }

        None
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
