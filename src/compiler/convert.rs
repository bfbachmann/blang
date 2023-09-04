use std::collections::HashMap;

use inkwell::context::Context;
use inkwell::types::AsTypeRef;
use inkwell::types::{
    AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, StructType,
};
use inkwell::AddressSpace;
use llvm_sys::core::LLVMFunctionType;
use llvm_sys::prelude::LLVMTypeRef;

use crate::analyzer::func::RichFnSig;
use crate::analyzer::r#struct::RichStructType;
use crate::analyzer::r#type::{RichType, TypeId};

/// Gets the LLVM basic type that corresponds to the given type.
pub fn to_basic_type<'a>(
    ctx: &'a Context,
    types: &HashMap<TypeId, RichType>,
    typ: &RichType,
) -> BasicTypeEnum<'a> {
    match typ {
        RichType::Bool => ctx.bool_type().as_basic_type_enum(),
        RichType::I64 => ctx.i64_type().as_basic_type_enum(),
        RichType::String => ctx
            .i32_type()
            .ptr_type(AddressSpace::default())
            .as_basic_type_enum(),
        RichType::Struct(struct_type) => {
            to_struct_type(ctx, types, struct_type).as_basic_type_enum()
        }
        RichType::Function(fn_sig) => to_fn_type(ctx, &types, fn_sig)
            .ptr_type(AddressSpace::default())
            .as_basic_type_enum(),
        RichType::Unknown(name) => {
            panic!("encountered unknown type {}", name)
        }
    }
}

/// Converts the given function signature into an LLVM `FunctionType`.
pub fn to_fn_type<'a>(
    ctx: &'a Context,
    types: &HashMap<TypeId, RichType>,
    sig: &RichFnSig,
) -> FunctionType<'a> {
    // Get return type.
    let ret_type = match &sig.ret_type_id {
        Some(type_id) => types.get(&type_id),
        None => None,
    };
    let mut ll_ret_type = to_any_type(ctx, types, ret_type);
    let mut ll_arg_types: Vec<BasicMetadataTypeEnum> = vec![];

    // If the return type is a structured type, we need to add an extra argument to the beginning
    // of the arguments list. This argument will be a pointer of the same type as the function
    // return value and will point to a location in memory (the caller's stack) to write
    // the structured return value. For example, if the function signature looks like this
    //
    //      fn new_person(): Person
    //
    // then the signature of the compiled function will essentially look like this
    //
    //      fn new_person(person: *Person)
    //
    // and the `person` pointer will be written to when assigning the return value.
    let ret_type = match &sig.ret_type_id {
        Some(type_id) => types.get(type_id),
        None => None,
    };
    if let Some(RichType::Struct(struct_type)) = ret_type {
        // Change the return type to void because, on return, we'll just be writing to the
        // pointer passed in the first argument.
        ll_ret_type = ctx.void_type().as_any_type_enum();
        let ll_struct_type = to_struct_type(ctx, types, struct_type);
        let ll_arg_type = ll_struct_type.ptr_type(AddressSpace::default());
        ll_arg_types.push(ll_arg_type.into());
    }

    // Get arg types.
    for arg in &sig.args {
        let arg_type = types.get(&arg.type_id).unwrap();
        ll_arg_types.push(to_metadata_type_enum(ctx, types, arg_type));
    }

    // Create the function type.
    let mut param_types: Vec<LLVMTypeRef> =
        ll_arg_types.iter().map(|val| val.as_type_ref()).collect();
    unsafe {
        FunctionType::new(LLVMFunctionType(
            ll_ret_type.as_type_ref(),
            param_types.as_mut_ptr(),
            param_types.len() as u32,
            false as i32,
        ))
    }
}

/// Returns the LLVM basic types corresponding to the given struct's field types.
fn get_struct_field_types<'a>(
    ctx: &'a Context,
    types: &HashMap<TypeId, RichType>,
    struct_type: &RichStructType,
) -> Vec<BasicTypeEnum<'a>> {
    struct_type
        .fields
        .iter()
        .map(|field| to_basic_type(ctx, types, types.get(&field.type_id).unwrap()))
        .collect()
}

/// Converts the given `RichStruct` to an LLVM `StructType`.
pub fn to_struct_type<'a>(
    ctx: &'a Context,
    types: &HashMap<TypeId, RichType>,
    struct_type: &RichStructType,
) -> StructType<'a> {
    // If the struct type already exists, just return it.
    if let Some(ll_struct_type) = ctx.get_struct_type(struct_type.name.as_str()) {
        return ll_struct_type;
    }

    // If the struct type has a name (i.e. it is not an inline type declaration), define it with
    // its type name. Otherwise, we just define a new struct type in-line.
    if !struct_type.name.is_empty() {
        let ll_struct_type = ctx.opaque_struct_type(struct_type.name.as_str());

        // Assemble the struct field types. It's important that we do this after creating
        // the opaque struct type to prevent infinite recursion on type conversion.
        let ll_field_types = get_struct_field_types(ctx, types, struct_type);

        // Create and return the LLVM struct type.
        ll_struct_type.set_body(ll_field_types.as_slice(), false);
        ll_struct_type
    } else {
        // Assemble the struct field types.
        let ll_field_types = get_struct_field_types(ctx, types, struct_type);

        // Create and return the LLVM struct type.
        ctx.struct_type(ll_field_types.as_slice(), false)
    }
}

/// Gets the LLVM "any" type that corresponds to the given type.
pub fn to_any_type<'a>(
    ctx: &'a Context,
    types: &HashMap<TypeId, RichType>,
    typ: Option<&RichType>,
) -> AnyTypeEnum<'a> {
    match typ {
        None => ctx.void_type().as_any_type_enum(),
        Some(t) => to_basic_type(ctx, types, t).as_any_type_enum(),
    }
}

/// Gets the LLVM metadata type that corresponds to the given type.
pub fn to_metadata_type_enum<'a>(
    ctx: &'a Context,
    types: &HashMap<TypeId, RichType>,
    typ: &RichType,
) -> BasicMetadataTypeEnum<'a> {
    match typ {
        RichType::I64 => BasicMetadataTypeEnum::from(ctx.i64_type()),
        RichType::Bool => BasicMetadataTypeEnum::from(ctx.bool_type()),
        RichType::String => {
            BasicMetadataTypeEnum::from(ctx.i32_type().ptr_type(AddressSpace::default()))
        }
        struct_type @ RichType::Struct(_) => BasicMetadataTypeEnum::from(
            to_basic_type(ctx, types, struct_type).ptr_type(AddressSpace::default()),
        ),
        RichType::Function(func) => {
            let fn_type = types.get(&func.type_id).unwrap();
            BasicMetadataTypeEnum::from(to_basic_type(ctx, types, fn_type))
        }
        other => panic!("unsupported type {}", other),
    }
}
