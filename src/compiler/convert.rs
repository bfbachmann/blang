use inkwell::context::Context;
use inkwell::types::{AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum};
use inkwell::AddressSpace;

use crate::parser::r#type::Type;

/// Gets the LLVM basic type that corresponds to the given type.
pub fn to_basic_type<'a>(context: &'a Context, typ: &Type) -> BasicTypeEnum<'a> {
    match typ {
        Type::Bool => context.bool_type().as_basic_type_enum(),
        Type::I64 => context.i64_type().as_basic_type_enum(),
        Type::String => context
            .i32_type()
            .ptr_type(AddressSpace::default())
            .as_basic_type_enum(),
        other => {
            panic!("invalid basic type {other}");
        }
    }
}

/// Gets the LLVM "any" type that corresponds to the given type.
pub fn to_any_type<'a>(context: &'a Context, typ: Option<&Type>) -> AnyTypeEnum<'a> {
    match typ {
        None => context.void_type().as_any_type_enum(),
        Some(t) => to_basic_type(context, t).as_any_type_enum(),
        // TODO: function types
    }
}

/// Gets the LLVM metadata type that corresponds to the given type.
pub fn to_metadata_type_enum<'a>(context: &'a Context, typ: &Type) -> BasicMetadataTypeEnum<'a> {
    match typ {
        Type::I64 => BasicMetadataTypeEnum::from(context.i64_type()),
        Type::Bool => BasicMetadataTypeEnum::from(context.bool_type()),
        Type::String => {
            BasicMetadataTypeEnum::from(context.i32_type().ptr_type(AddressSpace::default()))
        }
        other => panic!("unsupported type {}", other),
    }
}
