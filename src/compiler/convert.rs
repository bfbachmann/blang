use inkwell::context::Context;
use inkwell::types::{AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum};
use inkwell::AddressSpace;

use crate::analyzer::r#type::RichType;


/// Gets the LLVM basic type that corresponds to the given type.
pub fn to_basic_type<'a>(context: &'a Context, typ: &RichType) -> BasicTypeEnum<'a> {
    match typ {
        RichType::Bool => context.bool_type().as_basic_type_enum(),
        RichType::I64 => context.i64_type().as_basic_type_enum(),
        RichType::String => context
            .i32_type()
            .ptr_type(AddressSpace::default())
            .as_basic_type_enum(),
        other => {
            panic!("invalid basic type {other}");
        }
    }
}

/// Gets the LLVM "any" type that corresponds to the given type.
pub fn to_any_type<'a>(context: &'a Context, typ: Option<&RichType>) -> AnyTypeEnum<'a> {
    match typ {
        None => context.void_type().as_any_type_enum(),
        Some(t) => to_basic_type(context, t).as_any_type_enum(),
        // TODO: function types
    }
}

/// Gets the LLVM metadata type that corresponds to the given type.
pub fn to_metadata_type_enum<'a>(
    context: &'a Context,
    typ: &RichType,
) -> BasicMetadataTypeEnum<'a> {
    match typ {
        RichType::I64 => BasicMetadataTypeEnum::from(context.i64_type()),
        RichType::Bool => BasicMetadataTypeEnum::from(context.bool_type()),
        RichType::String => {
            BasicMetadataTypeEnum::from(context.i32_type().ptr_type(AddressSpace::default()))
        }
        other => panic!("unsupported type {}", other),
    }
}
