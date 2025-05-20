use std::collections::HashMap;

use inkwell::context::Context;
use inkwell::targets::TargetMachine;
use inkwell::types::{
    AnyType, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, IntType, StructType,
};
use inkwell::types::{ArrayType, AsTypeRef};
use inkwell::values::IntValue;
use inkwell::AddressSpace;
use llvm_sys::core::LLVMFunctionType;
use llvm_sys::prelude::LLVMTypeRef;

use crate::analyzer::ast::array::AArrayType;
use crate::analyzer::ast::func::AFnSig;
use crate::analyzer::ast::r#enum::AEnumType;
use crate::analyzer::ast::r#struct::AStructType;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::tuple::ATupleType;
use crate::analyzer::mangling::mangle_type;
use crate::analyzer::prog_context::Monomorphization;
use crate::analyzer::type_store::{GetType, TypeKey, TypeStore};

/// Converts types from the Blang analyzer to LLVM types.
pub struct TypeConverter<'a> {
    ctx: &'a Context,
    type_store: &'a TypeStore,
    type_monomorphizations: &'a HashMap<TypeKey, Monomorphization>,
    ll_target_machine: &'a TargetMachine,
    type_mapping: HashMap<TypeKey, TypeKey>,
}

impl<'a> GetType for TypeConverter<'a> {
    /// Returns the type that corresponds to the given key. This function will
    /// map `type_key` to another type key before performing the lookup it if
    /// falls within `self.type_key_mappings`.
    fn get_type(&self, type_key: TypeKey) -> &AType {
        self.type_store.get_type(self.map_type_key(type_key))
    }
}

impl<'a> TypeConverter<'a> {
    /// Creates a new type converter.
    pub fn new(
        ctx: &'a Context,
        type_store: &'a TypeStore,
        type_monomorphizations: &'a HashMap<TypeKey, Monomorphization>,
        ll_target_machine: &'a TargetMachine,
    ) -> TypeConverter<'a> {
        gen_intrinsic_types(ctx, ll_target_machine);

        TypeConverter {
            ctx,
            type_store,
            type_monomorphizations,
            ll_target_machine,
            type_mapping: HashMap::new(),
        }
    }

    /// Returns a reference to the current type mapping overlay on the type store.
    pub fn type_mapping(&self) -> &HashMap<TypeKey, TypeKey> {
        &self.type_mapping
    }

    /// Sets the type mapping to be used in type conversions.
    pub fn set_type_mapping(&mut self, type_mapping: HashMap<TypeKey, TypeKey>) {
        self.type_mapping = type_mapping;
    }

    /// Returns the type key that `type_key` should be replaced with according to the current
    /// type mapping. If there is none, just returns `type_key`.
    pub fn map_type_key(&self, type_key: TypeKey) -> TypeKey {
        match self.type_mapping.get(&type_key) {
            Some(tk) => *tk,
            None => type_key,
        }
    }

    /// Returns the LLVM basic type enum for the type associated with the given type key.
    pub fn get_basic_type(&self, type_key: TypeKey) -> BasicTypeEnum<'a> {
        self.to_basic_type(type_key)
    }

    /// Returns the LLVM function type for the type associated with the given type key.
    pub fn get_fn_type(&self, type_key: TypeKey) -> FunctionType<'a> {
        self.to_fn_type(self.get_type(type_key).to_fn_sig())
    }

    /// Returns the LLVM struct type for the type associated with the given type key.
    pub fn get_struct_type(&self, type_key: TypeKey) -> StructType<'a> {
        self.get_basic_type(type_key).into_struct_type()
    }

    /// Returns the LLVM array type for the type associated with the given type key.
    pub fn get_array_type(&self, type_key: TypeKey) -> ArrayType<'a> {
        self.get_basic_type(type_key).into_array_type()
    }

    /// Gets the LLVM basic type that corresponds to the given type.
    fn to_basic_type(&self, type_key: TypeKey) -> BasicTypeEnum<'a> {
        let typ = self.get_type(type_key);
        match typ {
            AType::Bool => self.ctx.bool_type().as_basic_type_enum(),

            AType::I8 | AType::U8 => self.ctx.i8_type().as_basic_type_enum(),

            AType::I16 | AType::U16 => self.ctx.i16_type().as_basic_type_enum(),

            AType::I32 | AType::U32 => self.ctx.i32_type().as_basic_type_enum(),

            AType::F32 => self.ctx.f32_type().as_basic_type_enum(),

            AType::I64 | AType::U64 => self.ctx.i64_type().as_basic_type_enum(),

            AType::F64 => self.ctx.f64_type().as_basic_type_enum(),

            AType::Int | AType::Uint => get_ptr_sized_int_type(self.ctx, self.ll_target_machine),

            AType::Str => self
                .ctx
                .get_struct_type(typ.name())
                .unwrap()
                .as_basic_type_enum(),

            AType::Char => self.ctx.i32_type().as_basic_type_enum(),

            AType::Struct(_) => self.to_struct_type(type_key).as_basic_type_enum(),

            AType::Enum(_) => self.enum_to_struct_type(type_key).as_basic_type_enum(),

            AType::Tuple(tuple_type) => self.tuple_to_struct_type(tuple_type).as_basic_type_enum(),

            AType::Array(array_type) => self.to_array_type(array_type).as_basic_type_enum(),

            AType::Function(_) => self
                .ctx
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),

            AType::Pointer(_) => self
                .ctx
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),

            AType::Generic(generic) => {
                panic!("unexpected generic type {}", generic.name)
            }

            AType::Spec(name) => {
                panic!("unexpected spec type {}", name)
            }

            AType::Unknown(name) => {
                panic!("unexpected unknown type {}", name)
            }
        }
    }

    /// Converts the given tuple type to its corresponding LLVM struct type.
    fn tuple_to_struct_type(&self, tuple_type: &ATupleType) -> StructType<'a> {
        // Assemble the tuple field types.
        let ll_field_types: Vec<BasicTypeEnum> = tuple_type
            .fields
            .iter()
            .map(|f| self.to_basic_type(f.type_key))
            .collect();

        // Create and return the LLVM struct type.
        self.ctx.struct_type(ll_field_types.as_slice(), false)
    }

    /// Converts the given function signature into an LLVM `FunctionType`.
    fn to_fn_type(&self, sig: &AFnSig) -> FunctionType<'a> {
        // Get return type.
        let mut ll_ret_type = match &sig.maybe_ret_type_key {
            None => self.ctx.void_type().as_any_type_enum(),
            Some(tk) => self.to_basic_type(*tk).as_any_type_enum(),
        };
        let mut ll_arg_types: Vec<BasicMetadataTypeEnum> = vec![];

        // If the return type is a structured type, we need to add an extra argument to the beginning
        // of the arguments list. This argument will be a pointer of the same type as the function
        // return value and will point to a location in memory (the caller's stack) to write
        // the structured return value. For example, if the function signature looks like this
        //
        //      fn new_person() -> Person
        //
        // then the signature of the compiled function will essentially look like this
        //
        //      fn new_person(person: *Person)
        //
        // and the `person` pointer will be written to when assigning the return value.
        let ret_type = sig.maybe_ret_type_key.map(|type_key| self.get_type(type_key));
        let extra_arg_type = match ret_type {
            Some(AType::Struct(_)) => Some(self.ctx.ptr_type(AddressSpace::default())),
            Some(AType::Enum(_)) => Some(self.ctx.ptr_type(AddressSpace::default())),
            Some(AType::Tuple(_)) => Some(self.ctx.ptr_type(AddressSpace::default())),
            Some(AType::Array(_)) => Some(self.ctx.ptr_type(AddressSpace::default())),
            _ => None,
        };

        if let Some(arg_type) = extra_arg_type {
            // Change the return type to void because, on return, we'll just be writing to the
            // pointer passed in the first argument.
            ll_ret_type = self.ctx.void_type().as_any_type_enum();
            ll_arg_types.push(arg_type.into());
        }

        // Get arg types.
        for arg in &sig.args {
            ll_arg_types.push(self.to_metadata_type_enum(arg.type_key));
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
    fn get_struct_field_types(&self, struct_type: &AStructType) -> Vec<BasicTypeEnum<'a>> {
        struct_type
            .fields
            .iter()
            .map(|field| self.to_basic_type(field.type_key))
            .collect()
    }

    /// Converts the given `struct_type` to an LLVM `StructType`.
    fn to_struct_type(&self, type_key: TypeKey) -> StructType<'a> {
        let struct_type = self.get_type(type_key).to_struct_type();

        // If the struct type already exists, just return it.
        let mangled_name = mangle_type(
            self,
            type_key,
            self.type_mapping(),
            self.type_monomorphizations,
        );
        if let Some(ll_struct_type) = self.ctx.get_struct_type(&mangled_name) {
            return ll_struct_type;
        }

        let ll_struct_type = self.ctx.opaque_struct_type(&mangled_name);

        // Assemble the struct field types. It's important that we do this after creating
        // the opaque struct type to prevent infinite recursion on type conversion.
        let ll_field_types = self.get_struct_field_types(struct_type);

        // Create and return the LLVM struct type.
        ll_struct_type.set_body(ll_field_types.as_slice(), false);
        ll_struct_type
    }

    /// Converts the given `array_type` to an LLVM `ArrayType`.
    fn to_array_type(&self, array_type: &AArrayType) -> ArrayType<'a> {
        match &array_type.maybe_element_type_key {
            Some(tk) => {
                let ll_element_type = self.to_basic_type(*tk);
                ll_element_type.array_type(array_type.len as u32)
            }
            None => self.ctx.i8_type().array_type(0),
        }
    }

    /// Converts the given `enum_type` to an LLVM `StructType`.
    fn enum_to_struct_type(&self, type_key: TypeKey) -> StructType<'a> {
        // If the corresponding LLVM struct type already exists, just return it.
        let mangled_name = mangle_type(
            self.type_store,
            type_key,
            self.type_mapping(),
            self.type_monomorphizations,
        );
        if let Some(ll_struct_type) = self.ctx.get_struct_type(&mangled_name) {
            return ll_struct_type;
        }

        // Figure out how many bytes we need to store the variant number based on how many
        // variants there are.
        let enum_type = self.get_type(type_key).to_enum_type();
        let tag_bytes = enum_variant_num_field_size(enum_type.variants.len() as u64);
        let ll_tag_type = self.int_type_with_size(tag_bytes);

        // Create the struct type with two fields. The first stores the enum variant number and the
        // second stores the enum variant value, if any. We'll omit the second field in cases where
        // none of the enum variants contain a value.
        let ll_enum_type = self.ctx.opaque_struct_type(&mangled_name);

        let max_variant_size = self.max_enum_variant_size(enum_type);
        if max_variant_size > 0 {
            let align_size = self.max_enum_variant_alignment(enum_type) as u64;
            let pad_size = (align_size - (tag_bytes as u64 % align_size)) % align_size;
            let payload_type = self
                .ctx
                .i8_type()
                .array_type((max_variant_size + pad_size) as u32);

            ll_enum_type.set_body(
                &[
                    ll_tag_type.as_basic_type_enum(),
                    payload_type.as_basic_type_enum(),
                ],
                false,
            );
        } else {
            ll_enum_type.set_body(&[ll_tag_type.as_basic_type_enum()], false);
        }

        ll_enum_type
    }

    /// Gets the LLVM metadata type that corresponds to the given type.
    fn to_metadata_type_enum(&self, type_key: TypeKey) -> BasicMetadataTypeEnum<'a> {
        let typ = self.get_type(type_key);
        if typ.is_composite() {
            BasicMetadataTypeEnum::from(self.ctx.ptr_type(AddressSpace::default()))
        } else {
            BasicMetadataTypeEnum::from(self.to_basic_type(type_key))
        }
    }

    /// Returns the size of the given type in bytes on the target machine, including padding. In
    /// other words, this returns the number of bytes required to hold the type in memory on the
    /// target system.
    pub fn size_of_type(&self, type_key: TypeKey) -> u64 {
        let ll_type = self.to_basic_type(type_key);
        self.ll_target_machine
            .get_target_data()
            .get_abi_size(&ll_type)
    }

    /// Returns the natural alignment of the given type in bytes.
    pub fn align_of_type(&self, type_key: TypeKey) -> u32 {
        let ll_type = self.to_basic_type(type_key);
        self.ll_target_machine
            .get_target_data()
            .get_abi_alignment(&ll_type)
    }

    /// Returns the size of the given type in bytes as an LLVM constant integer.
    pub fn const_int_size_of_type(&self, type_key: TypeKey) -> IntValue<'a> {
        self.get_const_int(self.size_of_type(type_key), false)
    }

    /// Converts `v` to an LLVM constant integer value.
    pub fn get_const_int(&self, v: u64, sign_extend: bool) -> IntValue<'a> {
        get_ptr_sized_int_type(self.ctx, self.ll_target_machine)
            .into_int_type()
            .const_int(v, sign_extend)
    }

    /// Returns the size of the largest enum variant in bytes.
    fn max_enum_variant_size(&self, enum_type: &AEnumType) -> u64 {
        enum_type
            .variants
            .iter()
            .fold(0, |acc, (_, v)| match v.maybe_type_key {
                Some(tk) => u64::max(acc, self.size_of_type(tk)),
                None => acc,
            })
    }

    /// Returns the maximum (i.e. strictest) padding required for any of the enum variant values.
    fn max_enum_variant_alignment(&self, enum_type: &AEnumType) -> u32 {
        enum_type
            .variants
            .iter()
            .fold(0, |acc, (_, v)| match v.maybe_type_key {
                Some(tk) => u32::max(acc, self.align_of_type(tk)),
                None => acc,
            })
    }

    fn int_type_with_size(&self, bytes_required: u32) -> IntType {
        match bytes_required {
            1 => self.ctx.i8_type(),
            2 => self.ctx.i16_type(),
            3 | 4 => self.ctx.i32_type(),
            _ => self.ctx.i64_type(),
        }
    }
}

/// Returns the LLVM type to be used in place of pointer-sized integer types which are sized
/// based on the target platform.
fn get_ptr_sized_int_type<'ctx>(
    ctx: &'ctx Context,
    target_machine: &TargetMachine,
) -> BasicTypeEnum<'ctx> {
    match target_machine.get_target_data().get_pointer_byte_size(None) {
        4 => ctx.i32_type().as_basic_type_enum(),
        2 => ctx.i16_type().as_basic_type_enum(),
        1 => ctx.i8_type().as_basic_type_enum(),
        _ => ctx.i64_type().as_basic_type_enum(),
    }
}

/// Generates type definitions for intrinsic types.
fn gen_intrinsic_types(ctx: &Context, target_machine: &TargetMachine) {
    // Create the LLVM struct type for the `str` type.
    {
        let ll_struct_type = ctx.opaque_struct_type(AType::Str.name());
        let ll_field_types: [BasicTypeEnum; 2] = [
            ctx.ptr_type(AddressSpace::default()).into(),
            get_ptr_sized_int_type(ctx, target_machine),
        ];
        ll_struct_type.set_body(&ll_field_types, false);
    }
}

fn enum_variant_num_field_size(num_variants: u64) -> u32 {
    let bits_required = 64 - num_variants.leading_zeros();
    bits_required.div_ceil(8)
}
