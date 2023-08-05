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
        RichType::Struct(struct_type) => {
            if let Some(typ) = context.get_struct_type(struct_type.name.as_str()) {
                typ.as_basic_type_enum()
            } else {
                let field_types: Vec<BasicTypeEnum> = struct_type
                    .fields
                    .iter()
                    .map(|field| to_basic_type(context, &field.typ))
                    .collect();
                context
                    .struct_type(field_types.as_slice(), false)
                    .as_basic_type_enum()
            }
        }
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
        struct_type @ RichType::Struct(_) => {
            BasicMetadataTypeEnum::from(to_basic_type(context, struct_type))
        }
        other => panic!("unsupported type {}", other),
    }
}
