use std::collections::HashMap;

use inkwell::context::Context;
use inkwell::types::{
    AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, StructType,
};
use inkwell::types::{ArrayType, AsTypeRef};
use inkwell::AddressSpace;
use llvm_sys::core::LLVMFunctionType;
use llvm_sys::prelude::LLVMTypeRef;

use crate::analyzer::ast::func::AFnSig;
use crate::analyzer::ast::r#enum::AEnumType;
use crate::analyzer::ast::r#struct::AStructType;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::tuple::ATupleType;
use crate::analyzer::type_store::{TypeKey, TypeStore};

/// Converts types from the Blang analyzer to LLVM types. This struct also caches mappings from
/// type keys to LLVM types to make type conversion faster.
pub struct TypeConverter<'ctx> {
    ctx: &'ctx Context,
    type_store: &'ctx TypeStore,
    ll_basic_types: HashMap<TypeKey, BasicTypeEnum<'ctx>>,
    ll_fn_types: HashMap<TypeKey, FunctionType<'ctx>>,
}

impl<'ctx> TypeConverter<'ctx> {
    /// Creates a new type converter.
    pub fn new(ctx: &'ctx Context, type_store: &'ctx TypeStore) -> TypeConverter<'ctx> {
        TypeConverter {
            ctx,
            type_store,
            ll_basic_types: Default::default(),
            ll_fn_types: Default::default(),
        }
    }

    /// Returns the LLVM basic type enum for the type associated with the given type key, either by
    /// locating the LLVM type in the cache (if it was already converted), or by converting and
    /// caching it.
    pub fn get_basic_type(&mut self, type_key: TypeKey) -> BasicTypeEnum<'ctx> {
        match self.ll_basic_types.get(&type_key) {
            Some(ll_type) => *ll_type,
            None => {
                let ll_type = to_basic_type(
                    self.ctx,
                    self.type_store,
                    self.type_store.must_get(type_key),
                );
                self.ll_basic_types.insert(type_key, ll_type);
                ll_type
            }
        }
    }

    /// Returns the LLVM function type for the type associated with the given type key, either by
    /// locating the LLVM type in the cache (if it was already converted), or by converting and
    /// caching it.
    pub fn get_fn_type(&mut self, type_key: TypeKey) -> FunctionType<'ctx> {
        match self.ll_fn_types.get(&type_key) {
            Some(f) => *f,
            None => {
                let ll_fn_type = to_fn_type(
                    self.ctx,
                    self.type_store,
                    self.type_store.must_get(type_key).to_fn_sig(),
                );
                self.ll_fn_types.insert(type_key, ll_fn_type);
                ll_fn_type
            }
        }
    }

    /// Returns the LLVM struct type for the type associated with the given type key, either by
    /// locating the LLVM type in the cache (if it was already converted), or by converting and
    /// caching it.
    pub fn get_struct_type(&mut self, type_key: TypeKey) -> StructType<'ctx> {
        self.get_basic_type(type_key).into_struct_type()
    }

    /// Returns the LLVM array type for the type associated with the given type key, either
    /// locating the LLVM type in the cache (if it was already converted), or by converting and
    /// caching it.
    pub fn get_array_type(&mut self, type_key: TypeKey) -> ArrayType<'ctx> {
        self.get_basic_type(type_key).into_array_type()
    }
}

/// Gets the LLVM basic type that corresponds to the given type.
fn to_basic_type<'ctx>(
    ctx: &'ctx Context,
    type_store: &TypeStore,
    typ: &AType,
) -> BasicTypeEnum<'ctx> {
    match typ {
        AType::Bool => ctx.bool_type().as_basic_type_enum(),

        AType::I64 => ctx.i64_type().as_basic_type_enum(),

        // TODO: There has to be a better way of representing `void *`... but then again, maybe not.
        // LLVM doesn't actually care about the pointee type, so really all pointers are treated
        // equally.
        AType::RawPtr => ctx
            .i64_type()
            .ptr_type(AddressSpace::default())
            .as_basic_type_enum(),

        AType::U64 => ctx.i64_type().as_basic_type_enum(),

        AType::Str => ctx
            .i8_type()
            .ptr_type(AddressSpace::default())
            .as_basic_type_enum(),

        AType::Struct(struct_type) => {
            to_struct_type(ctx, type_store, struct_type).as_basic_type_enum()
        }

        AType::Enum(enum_type) => enum_to_struct_type(ctx, enum_type).as_basic_type_enum(),

        AType::Tuple(tuple_type) => {
            tuple_to_struct_type(ctx, type_store, tuple_type).as_basic_type_enum()
        }

        AType::Array(array_type) => match &array_type.maybe_element_type_key {
            Some(tk) => {
                let ll_element_type = to_basic_type(ctx, type_store, type_store.must_get(*tk));
                ll_element_type
                    .array_type(array_type.len as u32)
                    .as_basic_type_enum()
            }
            None => ctx.i8_type().array_type(0).as_basic_type_enum(),
        },

        AType::Function(fn_sig) => to_fn_type(ctx, &type_store, fn_sig)
            .ptr_type(AddressSpace::default())
            .as_basic_type_enum(),

        AType::Pointer(ptr_type) => {
            let pointee_type = type_store.must_get(ptr_type.pointee_type_key);
            let ll_pointee_type = to_basic_type(ctx, type_store, pointee_type);
            ll_pointee_type
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum()
        }

        AType::Unknown(name) => {
            panic!("encountered unknown type {}", name)
        }
    }
}

/// Converts the given tuple type to its corresponding LLVM struct type.
fn tuple_to_struct_type<'ctx>(
    ctx: &'ctx Context,
    type_store: &TypeStore,
    tuple_type: &ATupleType,
) -> StructType<'ctx> {
    // Assemble the tuple field types.
    let ll_field_types: Vec<BasicTypeEnum> = tuple_type
        .fields
        .iter()
        .map(|f| to_basic_type(ctx, type_store, type_store.must_get(f.type_key)))
        .collect();

    // Create and return the LLVM struct type.
    ctx.struct_type(ll_field_types.as_slice(), false)
}

/// Converts the given function signature into an LLVM `FunctionType`.
fn to_fn_type<'ctx>(
    ctx: &'ctx Context,
    type_store: &TypeStore,
    sig: &AFnSig,
) -> FunctionType<'ctx> {
    // Get return type.
    let ret_type = match &sig.ret_type_key {
        Some(type_key) => Some(type_store.must_get(*type_key)),
        None => None,
    };
    let mut ll_ret_type = to_any_type(ctx, type_store, ret_type);
    let mut ll_arg_types: Vec<BasicMetadataTypeEnum> = vec![];

    // If the return type is a structured type, we need to add an extra argument to the beginning
    // of the arguments list. This argument will be a pointer of the same type as the function
    // return value and will point to a location in memory (the caller's stack) to write
    // the structured return value. For example, if the function signature looks like this
    //
    //      fn new_person() ~ Person
    //
    // then the signature of the compiled function will essentially look like this
    //
    //      fn new_person(person: *Person)
    //
    // and the `person` pointer will be written to when assigning the return value.
    let ret_type = match sig.ret_type_key {
        Some(type_key) => Some(type_store.must_get(type_key)),
        None => None,
    };
    let extra_arg_type = match ret_type {
        Some(AType::Struct(struct_type)) => {
            Some(to_struct_type(ctx, type_store, struct_type).ptr_type(AddressSpace::default()))
        }
        Some(AType::Enum(enum_type)) => {
            Some(enum_to_struct_type(ctx, enum_type).ptr_type(AddressSpace::default()))
        }
        Some(AType::Tuple(tuple_type)) => Some(
            tuple_to_struct_type(ctx, type_store, tuple_type).ptr_type(AddressSpace::default()),
        ),
        _ => None,
    };

    if let Some(arg_type) = extra_arg_type {
        // Change the return type to void because, on return, we'll just be writing to the
        // pointer passed in the first argument.
        ll_ret_type = ctx.void_type().as_any_type_enum();
        ll_arg_types.push(arg_type.into());
    }

    // Get arg types.
    for arg in &sig.args {
        let arg_type = type_store.must_get(arg.type_key);
        ll_arg_types.push(to_metadata_type_enum(ctx, type_store, arg_type));
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
fn get_struct_field_types<'ctx>(
    ctx: &'ctx Context,
    type_store: &TypeStore,
    struct_type: &AStructType,
) -> Vec<BasicTypeEnum<'ctx>> {
    struct_type
        .fields
        .iter()
        .map(|field| to_basic_type(ctx, type_store, type_store.must_get(field.type_key)))
        .collect()
}

/// Converts the given `struct_type` to an LLVM `StructType`.
fn to_struct_type<'ctx>(
    ctx: &'ctx Context,
    type_store: &TypeStore,
    struct_type: &AStructType,
) -> StructType<'ctx> {
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
        let ll_field_types = get_struct_field_types(ctx, type_store, struct_type);

        // Create and return the LLVM struct type.
        ll_struct_type.set_body(ll_field_types.as_slice(), false);
        ll_struct_type
    } else {
        // Assemble the struct field types.
        let ll_field_types = get_struct_field_types(ctx, type_store, struct_type);

        // Create and return the LLVM struct type.
        ctx.struct_type(ll_field_types.as_slice(), false)
    }
}

/// Converts the given `enum_type` to an LLVM `StructType`.
fn enum_to_struct_type<'ctx>(ctx: &'ctx Context, enum_type: &AEnumType) -> StructType<'ctx> {
    // If the corresponding LLVM struct type already exists, just return it.
    if let Some(ll_struct_type) = ctx.get_struct_type(enum_type.name.as_str()) {
        return ll_struct_type;
    }

    // Create the struct type with two fields. The first stores the enum variant number and the
    // second stores the enum variant value, if any.
    ctx.struct_type(
        &[
            ctx.i8_type().as_basic_type_enum(),
            ctx.i8_type()
                .array_type(enum_type.max_variant_size_bytes)
                .as_basic_type_enum(),
        ],
        false,
    )
}

/// Gets the LLVM "any" type that corresponds to the given type.
fn to_any_type<'ctx>(
    ctx: &'ctx Context,
    type_store: &TypeStore,
    typ: Option<&AType>,
) -> AnyTypeEnum<'ctx> {
    match typ {
        None => ctx.void_type().as_any_type_enum(),
        Some(t) => to_basic_type(ctx, type_store, t).as_any_type_enum(),
    }
}

/// Gets the LLVM metadata type that corresponds to the given type.
fn to_metadata_type_enum<'ctx>(
    ctx: &'ctx Context,
    type_store: &TypeStore,
    typ: &AType,
) -> BasicMetadataTypeEnum<'ctx> {
    match typ {
        AType::Struct(_) | AType::Tuple(_) | AType::Enum(_) => BasicMetadataTypeEnum::from(
            to_basic_type(ctx, type_store, typ).ptr_type(AddressSpace::default()),
        ),

        other => BasicMetadataTypeEnum::from(to_basic_type(ctx, type_store, other)),
    }
}
