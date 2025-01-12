use std::collections::HashMap;

use inkwell::context::Context;
use inkwell::targets::TargetMachine;
use inkwell::types::{
    AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, IntType,
    StructType,
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
use crate::analyzer::type_store::{GetType, TypeKey, TypeStore};

/// Converts types from the Blang analyzer to LLVM types.
pub struct TypeConverter<'ctx> {
    ctx: &'ctx Context,
    type_store: &'ctx TypeStore,
    ll_target_machine: &'ctx TargetMachine,
    type_mapping: HashMap<TypeKey, TypeKey>,
}

impl<'ctx> GetType for TypeConverter<'ctx> {
    /// Returns the type that corresponds to the given key. This function will
    /// map `type_key` to another type key before performing the lookup it if
    /// falls within `self.type_key_mappings`.
    fn get_type(&self, type_key: TypeKey) -> &AType {
        self.type_store.get_type(self.map_type_key(type_key))
    }
}

impl<'ctx> TypeConverter<'ctx> {
    /// Creates a new type converter.
    pub fn new(
        ctx: &'ctx Context,
        type_store: &'ctx TypeStore,
        ll_target_machine: &'ctx TargetMachine,
    ) -> TypeConverter<'ctx> {
        gen_intrinsic_types(ctx, ll_target_machine);

        TypeConverter {
            ctx,
            type_store,
            ll_target_machine,
            type_mapping: Default::default(),
        }
    }

    /// Sets the given mapping as a sort of overlay on the type store. This mapping will be used
    /// to translate type keys into other type keys before they're used. We're doing this to
    /// make monomorphization automatic.
    pub fn set_type_mapping(&mut self, mapping: HashMap<TypeKey, TypeKey>) {
        self.type_mapping = mapping;
    }

    /// Returns a reference to the current type mapping overlay on the type store.
    pub fn type_mapping(&self) -> &HashMap<TypeKey, TypeKey> {
        &self.type_mapping
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
    pub fn get_basic_type(&mut self, type_key: TypeKey) -> BasicTypeEnum<'ctx> {
        self.to_basic_type(self.get_type(type_key))
    }

    /// Returns the LLVM function type for the type associated with the given type key.
    pub fn get_fn_type(&mut self, type_key: TypeKey) -> FunctionType<'ctx> {
        self.to_fn_type(self.get_type(type_key).to_fn_sig())
    }

    /// Returns the LLVM struct type for the type associated with the given type key.
    pub fn get_struct_type(&mut self, type_key: TypeKey) -> StructType<'ctx> {
        self.get_basic_type(type_key).into_struct_type()
    }

    /// Returns the LLVM array type for the type associated with the given type key.
    pub fn get_array_type(&mut self, type_key: TypeKey) -> ArrayType<'ctx> {
        self.get_basic_type(type_key).into_array_type()
    }

    /// Gets the LLVM basic type that corresponds to the given type.
    fn to_basic_type(&self, typ: &AType) -> BasicTypeEnum<'ctx> {
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

            AType::Struct(struct_type) => self.to_struct_type(struct_type).as_basic_type_enum(),

            AType::Enum(enum_type) => self.enum_to_struct_type(enum_type).as_basic_type_enum(),

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
    fn tuple_to_struct_type(&self, tuple_type: &ATupleType) -> StructType<'ctx> {
        // Assemble the tuple field types.
        let ll_field_types: Vec<BasicTypeEnum> = tuple_type
            .fields
            .iter()
            .map(|f| self.to_basic_type(self.get_type(f.type_key)))
            .collect();

        // Create and return the LLVM struct type.
        self.ctx.struct_type(ll_field_types.as_slice(), false)
    }

    /// Converts the given function signature into an LLVM `FunctionType`.
    fn to_fn_type(&self, sig: &AFnSig) -> FunctionType<'ctx> {
        // Get return type.
        let ret_type = match &sig.maybe_ret_type_key {
            Some(type_key) => Some(self.get_type(*type_key)),
            None => None,
        };
        let mut ll_ret_type = self.to_any_type(ret_type);
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
        let ret_type = match sig.maybe_ret_type_key {
            Some(type_key) => Some(self.get_type(type_key)),
            None => None,
        };
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
            let arg_type = self.get_type(arg.type_key);
            ll_arg_types.push(self.to_metadata_type_enum(arg_type));
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
    fn get_struct_field_types(&self, struct_type: &AStructType) -> Vec<BasicTypeEnum<'ctx>> {
        struct_type
            .fields
            .iter()
            .map(|field| self.to_basic_type(self.get_type(field.type_key)))
            .collect()
    }

    /// Converts the given `struct_type` to an LLVM `StructType`.
    fn to_struct_type(&self, struct_type: &AStructType) -> StructType<'ctx> {
        // If the struct type already exists, just return it.
        if let Some(ll_struct_type) = self.ctx.get_struct_type(struct_type.mangled_name.as_str()) {
            return ll_struct_type;
        }

        // If the struct type has a name (i.e. it is not an inline type declaration), define it with
        // its type name. Otherwise, we just define a new struct type in-line.
        if !struct_type.name.is_empty() {
            let ll_struct_type = self
                .ctx
                .opaque_struct_type(struct_type.mangled_name.as_str());

            // Assemble the struct field types. It's important that we do this after creating
            // the opaque struct type to prevent infinite recursion on type conversion.
            let ll_field_types = self.get_struct_field_types(struct_type);

            // Create and return the LLVM struct type.
            ll_struct_type.set_body(ll_field_types.as_slice(), false);
            ll_struct_type
        } else {
            // Assemble the struct field types.
            let ll_field_types = self.get_struct_field_types(struct_type);

            // Create and return the LLVM struct type.
            self.ctx.struct_type(ll_field_types.as_slice(), false)
        }
    }

    /// Converts the given `array_type` to an LLVM `ArrayType`.
    fn to_array_type(&self, array_type: &AArrayType) -> ArrayType<'ctx> {
        match &array_type.maybe_element_type_key {
            Some(tk) => {
                let ll_element_type = self.to_basic_type(self.get_type(*tk));
                ll_element_type.array_type(array_type.len as u32)
            }
            None => self.ctx.i8_type().array_type(0),
        }
    }

    /// Converts the given `enum_type` to an LLVM `StructType`.
    fn enum_to_struct_type(&self, enum_type: &AEnumType) -> StructType<'ctx> {
        // If the corresponding LLVM struct type already exists, just return it.
        if let Some(ll_struct_type) = self.ctx.get_struct_type(enum_type.mangled_name.as_str()) {
            return ll_struct_type;
        }

        // Figure out how many bytes we need to store the variant number based on how many
        // variants there are.
        let ll_variant_num_type = self.enum_variant_num_field_type(enum_type.variants.len() as u64);

        // Create the struct type with two fields. The first stores the enum variant number and the
        // second stores the enum variant value, if any. We'll omit the second field in cases where
        // none of the enum variants contain a value.
        let ll_enum_type = self.ctx.opaque_struct_type(enum_type.mangled_name.as_str());
        let has_any_value = enum_type
            .variants
            .values()
            .find(|v| v.maybe_type_key.is_some())
            .is_some();

        if has_any_value {
            ll_enum_type.set_body(
                &[
                    ll_variant_num_type.as_basic_type_enum(),
                    self.ctx
                        .i8_type()
                        .array_type(self.max_enum_variant_size(enum_type) as u32)
                        .as_basic_type_enum(),
                ],
                false,
            );
        } else {
            ll_enum_type.set_body(&[ll_variant_num_type.as_basic_type_enum()], false);
        }

        ll_enum_type
    }

    /// Returns the LLVM IntType required to store the given number of enum variants.
    pub(crate) fn enum_variant_num_field_type(&self, num_variants: u64) -> IntType<'ctx> {
        let bits_required = 64 - num_variants.leading_zeros();
        let bytes_required = (bits_required + 7) / 8;
        match bytes_required {
            1 => self.ctx.i8_type(),
            2 => self.ctx.i16_type(),
            3 | 4 => self.ctx.i32_type(),
            _ => self.ctx.i64_type(),
        }
    }

    /// Gets the LLVM "any" type that corresponds to the given type.
    fn to_any_type(&self, typ: Option<&AType>) -> AnyTypeEnum<'ctx> {
        match typ {
            None => self.ctx.void_type().as_any_type_enum(),
            Some(t) => self.to_basic_type(t).as_any_type_enum(),
        }
    }

    /// Gets the LLVM metadata type that corresponds to the given type.
    fn to_metadata_type_enum(&self, typ: &AType) -> BasicMetadataTypeEnum<'ctx> {
        if typ.is_composite() {
            BasicMetadataTypeEnum::from(self.ctx.ptr_type(AddressSpace::default()))
        } else {
            BasicMetadataTypeEnum::from(self.to_basic_type(typ))
        }
    }

    /// Returns the size of the given type in bytes on the target machine, including padding. In
    /// other words, this returns the number of bytes required to hold the type in memory on the
    /// target system.
    pub fn size_of_type(&self, type_key: TypeKey) -> u64 {
        let ll_type = self.to_basic_type(self.get_type(type_key));
        self.ll_target_machine
            .get_target_data()
            .get_store_size(&ll_type)
    }

    /// Returns the natural alignment of the given type in bytes.
    pub fn align_of_type(&self, type_key: TypeKey) -> u32 {
        let ll_type = self.to_basic_type(self.get_type(type_key));
        self.ll_target_machine
            .get_target_data()
            .get_abi_alignment(&ll_type)
    }

    /// Returns the size of the given type in bytes as an LLVM constant integer.
    pub fn const_int_size_of_type(&self, type_key: TypeKey) -> IntValue<'ctx> {
        self.get_const_int(self.size_of_type(type_key), false)
    }

    /// Converts `v` to an LLVM constant integer value.
    pub fn get_const_int(&self, v: u64, sign_extend: bool) -> IntValue<'ctx> {
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
