use inkwell::attributes::Attribute;
use inkwell::context::Context;
use inkwell::types::AsTypeRef;
use inkwell::types::{
    AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, StructType,
};
use inkwell::AddressSpace;
use llvm_sys::core::LLVMFunctionType;
use llvm_sys::prelude::LLVMTypeRef;
use std::collections::VecDeque;

use crate::analyzer::func::RichFnSig;
use crate::analyzer::r#struct::RichStruct;
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
        RichType::Struct(struct_type) => to_struct_type(context, struct_type).as_basic_type_enum(),
        RichType::Function(fn_sig) => to_fn_type(context, fn_sig)
            .ptr_type(AddressSpace::default())
            .as_basic_type_enum(),
        other => {
            panic!("invalid basic type {other}");
        }
    }
}

/// Converts the given function signature into an LLVM `FunctionType`.
pub fn to_fn_type<'a>(context: &'a Context, sig: &RichFnSig) -> FunctionType<'a> {
    // Get return type.
    let mut ret_type = to_any_type(context, sig.return_type.as_ref());

    // Get arg types.
    let mut arg_types: VecDeque<BasicMetadataTypeEnum> = sig
        .args
        .iter()
        .map(|a| to_metadata_type_enum(context, &a.typ))
        .collect();

    // If the return type is a structured type, we need to add an extra argument to the beginning
    // of the arguments list. This argument will be a pointer of the same type as the function
    // return value and will point to a location in memory (the caller's stack) to write
    // the structured return value. For example, if the function signature looks like this
    //
    //      fn new_person(): Person
    //
    // then the signature of the compiled function will essentially look like this
    //
    //      fn new_person(Person* person)
    //
    // and the `person` pointer will be written to when assigning the return value.
    let type_attr: Attribute;
    if let Some(struct_type @ RichType::Struct(_)) = &sig.return_type {
        // Change the return type to void because, on return, we'll just be writing to the
        // pointer passed in the first argument.
        ret_type = context.void_type().as_any_type_enum();

        // Add the pointer as the first argument. We're giving this argument the "sret" attribute
        // to tell LLVM that it will contain the function's return value upon return.
        let sret_attr = Attribute::get_named_enum_kind_id("sret");
        let arg_type = to_any_type(context, Some(struct_type));
        type_attr = context.create_type_attribute(
            sret_attr,
            arg_type
                .into_struct_type()
                .ptr_type(AddressSpace::default())
                .as_any_type_enum(),
        );
        arg_types.push_front(type_attr.get_type_value().into_pointer_type().into());
    }

    // Create the function type.
    let mut param_types: Vec<LLVMTypeRef> = arg_types.iter().map(|val| val.as_type_ref()).collect();
    unsafe {
        FunctionType::new(LLVMFunctionType(
            ret_type.as_type_ref(),
            param_types.as_mut_ptr(),
            param_types.len() as u32,
            false as i32,
        ))
    }
}

/// Converts the given `RichStruct` to an LLVM `StructType`.
pub fn to_struct_type<'a>(context: &'a Context, struct_type: &RichStruct) -> StructType<'a> {
    // If the struct type already exists, just return it.
    if let Some(llvm_struct_type) = context.get_struct_type(struct_type.name.as_str()) {
        return llvm_struct_type;
    }

    // Assemble the struct field types.
    let llvm_field_types: Vec<BasicTypeEnum> = struct_type
        .fields
        .iter()
        .map(|field| to_basic_type(context, &field.typ))
        .collect();

    // If the struct type has a name (i.e. it is not an inline type declaration), define it with
    // its type name. Otherwise, we just define a new struct type in-line.
    if !struct_type.name.is_empty() {
        let llvm_struct_type = context.opaque_struct_type(struct_type.name.as_str());
        llvm_struct_type.set_body(llvm_field_types.as_slice(), false);
        llvm_struct_type
    } else {
        context.struct_type(llvm_field_types.as_slice(), false)
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
