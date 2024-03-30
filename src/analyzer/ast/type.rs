use std::cmp::max;
use std::fmt;
use std::fmt::{Display, Formatter};

use crate::analyzer::ast::array::AArrayType;
use crate::analyzer::ast::func::AFnSig;
use crate::analyzer::ast::pointer::APointerType;
use crate::analyzer::ast::r#enum::AEnumType;
use crate::analyzer::ast::r#struct::AStructType;
use crate::analyzer::ast::tuple::ATupleType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeStore;
use crate::parser::ast::r#type::Type;

#[derive(Debug)]
pub enum AType {
    // Primitive types.
    Bool,
    U8,
    I8,
    U32,
    I32,
    I64,
    U64,
    Int,
    Uint,
    Str,

    // Composite types.
    Struct(AStructType),
    Enum(AEnumType),
    Tuple(ATupleType),
    Array(AArrayType),
    Function(Box<AFnSig>),
    Pointer(APointerType),

    /// Represents a type that did not pass semantic analysis and thus was never properly resolved.
    Unknown(String),
}

impl Display for AType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            AType::Bool => write!(f, "bool"),
            AType::Str => write!(f, "str"),
            AType::U8 => write!(f, "u8"),
            AType::I8 => write!(f, "i8"),
            AType::U32 => write!(f, "u32"),
            AType::I32 => write!(f, "i32"),
            AType::I64 => write!(f, "i64"),
            AType::U64 => write!(f, "u64"),
            AType::Int => write!(f, "int"),
            AType::Uint => write!(f, "uint"),
            AType::Struct(s) => write!(f, "{}", s),
            AType::Enum(e) => write!(f, "{}", e),
            AType::Tuple(t) => write!(f, "{}", t),
            AType::Array(a) => write!(f, "{}", a),
            AType::Function(func) => write!(f, "{}", func),
            AType::Pointer(typ) => write!(f, "*{}", typ),
            AType::Unknown(name) => write!(f, "{}", name),
        }
    }
}

impl PartialEq for AType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (AType::Bool, AType::Bool)
            | (AType::U8, AType::U8)
            | (AType::I8, AType::I8)
            | (AType::U32, AType::U32)
            | (AType::I32, AType::I32)
            | (AType::I64, AType::I64)
            | (AType::U64, AType::U64)
            | (AType::Int, AType::Int)
            | (AType::Uint, AType::Uint)
            | (AType::Str, AType::Str) => true,
            (AType::Struct(s1), AType::Struct(s2)) => s1 == s2,
            (AType::Enum(e1), AType::Enum(e2)) => e1 == e2,
            (AType::Tuple(t1), AType::Tuple(t2)) => t1 == t2,
            (AType::Array(t1), AType::Array(t2)) => t1 == t2,
            (AType::Function(f1), AType::Function(f2)) => *f1 == *f2,
            (AType::Pointer(t1), AType::Pointer(t2)) => t1 == t2,
            (_, _) => false,
        }
    }
}

impl AType {
    /// Analyzes `typ` and returns an analyzed version of it.
    pub fn from(ctx: &mut ProgramContext, typ: &Type) -> AType {
        match typ {
            Type::Unresolved(unresolved_type) => {
                let type_name = unresolved_type.name.as_str();

                // Check if the type has already been marked as invalid. If so, we should avoid
                // trying to resolve it and simply return the unknown type.
                if ctx.is_name_of_invalid_type(type_name) {
                    return AType::Unknown(type_name.to_string());
                }

                // If the type has already been analyzed, just return it.
                if let Some(struct_type) = ctx.get_struct_type(type_name) {
                    return AType::Struct(struct_type.clone());
                }
                if let Some(enum_type) = ctx.get_enum_type(type_name) {
                    return AType::Enum(enum_type.clone());
                }
                if let Some(fn_sig) = ctx.get_defined_fn_sig(type_name) {
                    return AType::from_fn_sig(fn_sig.clone());
                }
                if let Some(fn_type) = ctx.get_fn(type_name) {
                    return AType::from_fn_sig(fn_type.signature.clone());
                }

                // The type has not yet been analyzed, so make sure the type has at least been
                // declared somewhere and analyze it.
                if let Some(struct_type) = ctx.get_unchecked_struct_type(type_name) {
                    return AType::Struct(AStructType::from(ctx, &struct_type.clone(), false));
                }
                if let Some(enum_type) = ctx.get_unchecked_enum_type(type_name) {
                    return AType::Enum(AEnumType::from(ctx, &enum_type.clone()));
                }

                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::UndefType,
                    format_code!("type {} is not defined", type_name).as_str(),
                    unresolved_type,
                ));

                return AType::Unknown("<unknown>".to_string());
            }

            Type::Function(sig) => AType::from_fn_sig(AFnSig::from(ctx, &*sig)),

            Type::Struct(struct_type) => {
                let a_struct_type = AStructType::from(ctx, struct_type, true);
                return AType::Struct(a_struct_type);
            }

            Type::Enum(enum_type) => {
                let a_enum_type = AEnumType::from(ctx, enum_type);
                return AType::Enum(a_enum_type);
            }

            Type::Tuple(tuple_type) => {
                let a_tuple_type = ATupleType::from(ctx, tuple_type);
                return AType::Tuple(a_tuple_type);
            }

            Type::Array(array_type) => {
                let a_array_type = AArrayType::from(ctx, array_type);
                return AType::Array(a_array_type);
            }

            Type::Pointer(ptr_type) => {
                return AType::Pointer(APointerType::from(ctx, ptr_type));
            }
        }
    }

    /// Returns the mapping from parsed type to analyzed type for all primitives types.
    pub fn primitives() -> Vec<AType> {
        vec![
            AType::Bool,
            AType::U8,
            AType::I8,
            AType::U32,
            AType::I32,
            AType::I64,
            AType::U64,
            AType::Int,
            AType::Uint,
            AType::Str,
            AType::Unknown("<unknown>".to_string()),
            AType::Unknown("<none>".to_string()),
            AType::Unknown("Self".to_string()),
        ]
    }

    /// Returns the name assigned to this type. Note that some types (like tuples or struct types
    /// defined in-line) do not have names.
    pub fn name(&self) -> &str {
        match self {
            AType::Bool => "bool",
            AType::U8 => "u8",
            AType::I8 => "i8",
            AType::U32 => "u32",
            AType::I32 => "i32",
            AType::I64 => "i64",
            AType::U64 => "u64",
            AType::Int => "int",
            AType::Uint => "uint",
            AType::Str => "str",
            AType::Struct(t) => t.name.as_str(),
            AType::Enum(t) => t.name.as_str(),
            AType::Tuple(_) | AType::Pointer(_) | AType::Array(_) => "",
            AType::Function(t) => t.name.as_str(),
            AType::Unknown(name) => name.as_str(),
        }
    }

    /// Creates a new type from the given function signature.
    pub fn from_fn_sig(sig: AFnSig) -> AType {
        AType::Function(Box::new(sig))
    }

    /// Returns true if the two types are the same.
    ///  - For primitive types (i64, bool, etc), they must be exactly the same type.
    ///  - For struct types, they must be exactly the same type.
    ///  - For function types, they must have arguments of the same type in the same order and the
    ///    same return types.
    pub fn is_same_as(&self, ctx: &ProgramContext, other: &AType, ignore_mutability: bool) -> bool {
        match (self, other) {
            (AType::Function(f1), AType::Function(f2)) => f1.is_same_as(ctx, f2),
            (AType::Tuple(t1), AType::Tuple(t2)) => t1.is_same_as(ctx, t2),
            (AType::Array(a1), AType::Array(a2)) => a1.is_same_as(ctx, a2),
            (AType::Pointer(p1), AType::Pointer(p2)) => {
                let p1_pointee_type = ctx.must_get_type(p1.pointee_type_key);
                let p2_pointee_type = ctx.must_get_type(p2.pointee_type_key);
                let same_pointee_types = p1_pointee_type.is_same_as(ctx, p2_pointee_type, false);
                same_pointee_types && (ignore_mutability || p1.is_mut == p2.is_mut)
            }
            (a, b) => a == b,
        }
    }

    /// If this type contains the given type, returns some vector of types representing the type
    /// hierarchy. For example, if type A contains B, and B contains C, then
    ///
    ///     A.contains_type(C)
    ///
    /// returns the hierarchy
    ///
    ///     Some(vec![A, B, C])
    pub fn contains_type<'a>(
        &'a self,
        ctx: &'a ProgramContext,
        typ: &AType,
    ) -> Option<Vec<&AType>> {
        let mut hierarchy = vec![];
        match self.get_type_hierarchy(ctx, typ, &mut hierarchy) {
            true => Some(hierarchy),
            false => None,
        }
    }

    /// Returns true if this type contains the given type. If true, the given `hierarchy` Vec will
    /// be filled with the hierarchy from `self` to `typ`.
    fn get_type_hierarchy<'a>(
        &'a self,
        ctx: &'a ProgramContext,
        typ: &AType,
        hierarchy: &mut Vec<&'a AType>,
    ) -> bool {
        hierarchy.push(&self);

        return match self {
            AType::Bool
            | AType::U8
            | AType::I8
            | AType::U32
            | AType::I32
            | AType::I64
            | AType::U64
            | AType::Int
            | AType::Uint
            | AType::Str
            | AType::Function(_)
            | AType::Pointer(_)
            | AType::Unknown(_) => false,

            AType::Struct(s) => {
                for field in &s.fields {
                    let field_type = ctx.must_get_type(field.type_key);
                    if field_type == typ {
                        hierarchy.push(field_type);
                        return true;
                    } else if field_type.get_type_hierarchy(ctx, typ, hierarchy) {
                        return true;
                    }
                }

                false
            }

            AType::Enum(e) => {
                for variant in e.variants.values() {
                    if let Some(type_key) = variant.maybe_type_key {
                        let variant_type = ctx.must_get_type(type_key);
                        if variant_type == typ {
                            hierarchy.push(variant_type);
                            return true;
                        } else if variant_type.get_type_hierarchy(ctx, typ, hierarchy) {
                            return true;
                        }
                    }
                }

                false
            }

            AType::Tuple(t) => {
                for field in &t.fields {
                    let field_type = ctx.must_get_type(field.type_key);
                    if field_type == typ {
                        hierarchy.push(field_type);
                        return true;
                    } else if field_type.get_type_hierarchy(ctx, typ, hierarchy) {
                        return true;
                    }
                }

                false
            }

            AType::Array(a) => match &a.maybe_element_type_key {
                Some(key) => {
                    let element_type = ctx.must_get_type(*key);
                    if element_type == typ {
                        hierarchy.push(element_type);
                        return true;
                    }

                    element_type.get_type_hierarchy(ctx, typ, hierarchy)
                }

                None => false,
            },
        };
    }

    /// Returns true only if this type is moved on assignment or when passed as an argument.
    pub fn requires_move(&self) -> bool {
        self.is_composite()
    }

    /// Returns true if this type is unknown.
    pub fn is_unknown(&self) -> bool {
        matches!(self, AType::Unknown(_))
    }

    /// Returns true if this is a numeric type.
    pub fn is_numeric(&self) -> bool {
        matches!(
            self,
            AType::U8
                | AType::I8
                | AType::U32
                | AType::I32
                | AType::U64
                | AType::I64
                | AType::Int
                | AType::Uint
        )
    }

    /// Returns true if this is a pointer type.
    pub fn is_pointer(&self) -> bool {
        matches!(self, AType::Pointer(_))
    }

    /// Returns true if this is a mutable pointer type.
    pub fn is_mut_pointer(&self) -> bool {
        matches!(self, AType::Pointer(APointerType { is_mut: true, .. }))
    }

    /// Returns true if this is a function type.
    pub fn is_fn(&self) -> bool {
        matches!(self, AType::Function(_))
    }

    /// Returns true if arithmetic operations on this type should be signed. Otherwise, this type
    /// either doesn't support arithmetic operations, or requires unsigned operations.
    pub fn is_signed(&self) -> bool {
        match self {
            AType::I8 | AType::I32 | AType::I64 | AType::Int => true,
            AType::Bool
            | AType::Str
            | AType::U8
            | AType::U32
            | AType::U64
            | AType::Uint
            | AType::Struct(_)
            | AType::Enum(_)
            | AType::Tuple(_)
            | AType::Array(_)
            | AType::Function(_)
            | AType::Pointer(_)
            | AType::Unknown(_) => false,
        }
    }

    /// Returns the size of this type (i.e. the amount of memory required to store it) in bytes.
    /// Note that this WILL NOT necessarily be the actual size of the type in the generated
    /// machine code, as that is partially determined by LLVM based on the target arch.
    /// This function should only be used to get a sense for the minimum size of a given type.
    pub fn size_bytes(&self, type_store: &TypeStore) -> u32 {
        match self {
            // Bools are 1 byte.
            AType::Bool | AType::U8 | AType::I8 => 1,

            // All the following types are 32 bits (4 bytes).
            AType::U32 | AType::I32 => 4,

            // All the following types are 64 bits (8 bytes).
            AType::I64 | AType::U64 | AType::Function(_) => 8,

            // `int`s, `uint`s, and pointers are sized based on the target platform (64 or 32 bits, generally).
            AType::Int | AType::Uint | AType::Pointer(_) => {
                (type_store.get_target_ptr_width() / 8) as u32
            }

            // `str`s are composed of a pointer and an integer.
            AType::Str => {
                (type_store.get_target_ptr_width() / 8) as u32 + AType::Int.size_bytes(type_store)
            }

            // The size of a struct type is the sum of the sizes of all of its fields.
            AType::Struct(struct_type) => {
                let mut size = 0;
                for field in &struct_type.fields {
                    let field_type = type_store.must_get(field.type_key);
                    size += field_type.size_bytes(type_store);
                }

                size
            }

            // The size of an enum type is 1 byte (to hold the variant number) plus the greatest
            // size of all of its variants.
            AType::Enum(enum_type) => {
                let mut size = 0;
                for variant in enum_type.variants.values() {
                    if let Some(type_key) = variant.maybe_type_key {
                        let variant_type = type_store.must_get(type_key);
                        size = max(size, variant_type.size_bytes(type_store));
                    }
                }

                size + 1
            }

            AType::Tuple(tuple_type) => {
                let mut size = 0;
                for field in &tuple_type.fields {
                    let field_type = type_store.must_get(field.type_key);
                    size += field_type.size_bytes(type_store)
                }

                size
            }

            AType::Array(array_type) => match &array_type.maybe_element_type_key {
                Some(key) => {
                    let element_type = type_store.must_get(*key);
                    element_type.size_bytes(type_store) * array_type.len as u32
                }

                None => 0,
            },

            AType::Unknown(_) => 0,
        }
    }

    /// Returns true if this is a composite type (i.e. a type that can contain other types).
    pub fn is_composite(&self) -> bool {
        matches!(
            self,
            AType::Struct(_) | AType::Enum(_) | AType::Tuple(_) | AType::Array(_)
        )
    }

    /// Returns the struct type corresponding to this type. Panics if this type is not a
    /// struct type.
    pub fn to_struct_type(&self) -> &AStructType {
        match self {
            AType::Struct(struct_type) => struct_type,
            _ => panic!("type {} is not a struct", self),
        }
    }

    /// Returns the pointer type corresponding to this type. Panics if this type is not
    /// a pointer type.
    pub fn to_ptr_type(&self) -> &APointerType {
        match self {
            AType::Pointer(ptr_type) => ptr_type,
            _ => panic!("type {} is not a pointer", self),
        }
    }

    /// Returns the enum type corresponding to this type. Panics if this type is not an
    /// enum type.
    pub fn to_enum_type(&self) -> &AEnumType {
        match self {
            AType::Enum(enum_type) => enum_type,
            _ => panic!("type {} is not am enum", self),
        }
    }

    /// Returns the array type corresponding to this type. Panics if this type is not an
    /// array type.
    pub fn to_array_type(&self) -> &AArrayType {
        match self {
            AType::Array(array_type) => array_type,
            _ => panic!("type {} is not am array", self),
        }
    }

    /// Converts the type to a function signature. Panics if the type is not a function type.
    pub fn to_fn_sig(&self) -> &AFnSig {
        match self {
            AType::Function(sig) => sig,
            _ => panic!("type {} is not a function", self),
        }
    }

    /// Returns true if the type is templated.
    pub fn is_templated(&self) -> bool {
        match self {
            AType::Function(sig) => sig.is_templated(),
            _ => false,
        }
    }

    /// Returns true if the type is `bool`.
    pub fn is_bool(&self) -> bool {
        matches!(self, AType::Bool)
    }

    /// Returns a string containing a human-readable version of the type.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        match self {
            AType::Bool
            | AType::Str
            | AType::I8
            | AType::U8
            | AType::U32
            | AType::I32
            | AType::I64
            | AType::U64
            | AType::Int
            | AType::Uint => {
                format!("{}", self)
            }
            AType::Struct(s) => format!("{}", s.display(ctx)),
            AType::Enum(e) => format!("{}", e.display(ctx)),
            AType::Tuple(t) => format!("{}", t.display(ctx)),
            AType::Array(a) => format!("{}", a.display(ctx)),
            AType::Function(func) => format!("{}", func.display(ctx, true)),
            AType::Pointer(t) => format!("{}", t.display(ctx)),
            AType::Unknown(name) => format!("{}", name),
        }
    }
}
