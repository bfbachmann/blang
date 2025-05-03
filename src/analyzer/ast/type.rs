use crate::analyzer::ast::array::AArrayType;
use crate::analyzer::ast::func::AFnSig;
use crate::analyzer::ast::generic::AGenericType;
use crate::analyzer::ast::params::AParams;
use crate::analyzer::ast::pointer::APointerType;
use crate::analyzer::ast::r#enum::AEnumType;
use crate::analyzer::ast::r#struct::AStructType;
use crate::analyzer::ast::spec::ASpecType;
use crate::analyzer::ast::tuple::ATupleType;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::codegen::convert::TypeConverter;
use crate::lexer::pos::Span;
use inkwell::context::Context;
use std::fmt;
use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, PartialEq)]
pub enum AType {
    // Primitive types.
    Bool,
    U8,
    I8,
    U16,
    I16,
    U32,
    I32,
    F32,
    I64,
    U64,
    F64,
    Int,
    Uint,
    Str,
    Char,

    // Composite types.
    Struct(AStructType),
    Enum(AEnumType),
    Tuple(ATupleType),
    Array(AArrayType),
    Function(Box<AFnSig>),
    Pointer(APointerType),

    /// Represents a type specification (a set of things one can do with a type,
    /// but not an actual concrete type).
    Spec(ASpecType),

    /// Represents a generic (parameterized) type.
    Generic(AGenericType),

    /// Represents a type that did not pass semantic analysis and thus was never properly resolved.
    Unknown(String),
}

impl Display for AType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            AType::Bool => write!(f, "bool"),
            AType::Str => write!(f, "str"),
            AType::Char => write!(f, "char"),
            AType::U8 => write!(f, "u8"),
            AType::I8 => write!(f, "i8"),
            AType::U16 => write!(f, "u16"),
            AType::I16 => write!(f, "i16"),
            AType::U32 => write!(f, "u32"),
            AType::I32 => write!(f, "i32"),
            AType::F32 => write!(f, "f32"),
            AType::I64 => write!(f, "i64"),
            AType::U64 => write!(f, "u64"),
            AType::F64 => write!(f, "f64"),
            AType::Int => write!(f, "int"),
            AType::Uint => write!(f, "uint"),
            AType::Struct(s) => write!(f, "{}", s),
            AType::Enum(e) => write!(f, "{}", e),
            AType::Spec(s) => write!(f, "{}", s),
            AType::Tuple(t) => write!(f, "{}", t),
            AType::Array(a) => write!(f, "{}", a),
            AType::Function(func) => write!(f, "{}", func),
            AType::Pointer(typ) => write!(f, "{}", typ),
            AType::Generic(g) => write!(f, "{}", g),
            AType::Unknown(name) => write!(f, "{}", name),
        }
    }
}

impl AType {
    /// Returns the mapping from parsed type to analyzed type for all primitives types.
    pub fn primitives() -> Vec<AType> {
        vec![
            AType::Bool,
            AType::U8,
            AType::I8,
            AType::U16,
            AType::I16,
            AType::U32,
            AType::I32,
            AType::F32,
            AType::I64,
            AType::U64,
            AType::F64,
            AType::Int,
            AType::Uint,
            AType::Str,
            AType::Char,
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
            AType::U16 => "u16",
            AType::I16 => "i16",
            AType::U32 => "u32",
            AType::I32 => "i32",
            AType::F32 => "f32",
            AType::I64 => "i64",
            AType::U64 => "u64",
            AType::F64 => "f64",
            AType::Int => "int",
            AType::Uint => "uint",
            AType::Str => "str",
            AType::Char => "char",
            AType::Struct(t) => t.name.as_str(),
            AType::Enum(t) => t.name.as_str(),
            AType::Spec(t) => t.name.as_str(),
            AType::Tuple(_) | AType::Pointer(_) | AType::Array(_) => "",
            AType::Function(t) => t.name.as_str(),
            AType::Generic(g) => g.name.as_str(),
            AType::Unknown(name) => name.as_str(),
        }
    }

    pub fn span(&self) -> Span {
        match self {
            AType::Struct(struct_type) => struct_type.span,
            AType::Enum(enum_type) => enum_type.span,
            AType::Function(fn_sig) => fn_sig.span,
            AType::Spec(spec_type) => spec_type.span,
            _ => Span::default(),
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
                let p1_pointee_type = ctx.get_type(p1.pointee_type_key);
                let p2_pointee_type = ctx.get_type(p2.pointee_type_key);
                let same_pointee_types = p1_pointee_type.is_same_as(ctx, p2_pointee_type, false);
                same_pointee_types && (ignore_mutability || p1.is_mut == p2.is_mut)
            }
            (a, b) => {
                if b.is_spec() {
                    // TODO: Check if type implements spec. At the moment, we're just assuming
                    // that the spec is satisfied by the type because this case should only
                    // happen when we're checking if a function signature matches that of a spec,
                    // so this works for now but isn't really robust long-term.
                    return true;
                }

                a == b
            }
        }
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
                | AType::I16
                | AType::U16
                | AType::U32
                | AType::I32
                | AType::F32
                | AType::U64
                | AType::I64
                | AType::F64
                | AType::Int
                | AType::Uint
        )
    }

    /// Returns true if this type is an integer type.
    pub fn is_integer(&self) -> bool {
        matches!(
            self,
            AType::U8
                | AType::I8
                | AType::U16
                | AType::I16
                | AType::U32
                | AType::I32
                | AType::U64
                | AType::I64
                | AType::Int
                | AType::Uint
        )
    }

    /// Returns true if this type is an enum type.
    pub fn is_enum(&self) -> bool {
        matches!(self, AType::Enum(_))
    }

    /// Returns true if this is a pointer type.
    pub fn is_any_ptr(&self) -> bool {
        matches!(self, AType::Pointer(_))
    }

    /// Returns true if this is a read-only pointer type.
    pub fn is_readonly_ptr(&self) -> bool {
        matches!(self, AType::Pointer(APointerType { is_mut: false, .. }))
    }

    /// Returns true if this is a mutating pointer type.
    pub fn is_mut_ptr(&self) -> bool {
        matches!(self, AType::Pointer(APointerType { is_mut: true, .. }))
    }

    /// Returns true if this is a function type.
    pub fn is_fn(&self) -> bool {
        matches!(self, AType::Function(_))
    }

    /// Returns true if this is a floating-point type.
    pub fn is_float(&self) -> bool {
        matches!(self, AType::F64 | AType::F32)
    }

    /// Returns true if this is a tuple type.
    pub fn is_tuple(&self) -> bool {
        matches!(self, AType::Tuple(_))
    }

    /// Returns true if this is a spec type.
    pub fn is_spec(&self) -> bool {
        matches!(self, AType::Spec(_))
    }

    /// Returns true if arithmetic operations on this type should be signed. Otherwise, this type
    /// either doesn't support arithmetic operations, or requires unsigned operations.
    pub fn is_signed(&self) -> bool {
        match self {
            AType::I8
            | AType::I16
            | AType::I32
            | AType::F32
            | AType::I64
            | AType::F64
            | AType::Int => true,

            AType::Bool
            | AType::Str
            | AType::Char
            | AType::U8
            | AType::U16
            | AType::U32
            | AType::U64
            | AType::Uint
            | AType::Struct(_)
            | AType::Enum(_)
            | AType::Spec(_)
            | AType::Tuple(_)
            | AType::Array(_)
            | AType::Function(_)
            | AType::Pointer(_)
            | AType::Generic(_)
            | AType::Unknown(_) => false,
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

    /// Returns the tuple type corresponding to this type. Panics if this type is not a
    /// tuple type.
    pub fn to_tuple_type(&self) -> &ATupleType {
        match self {
            AType::Tuple(tuple_type) => tuple_type,
            _ => panic!("type {} is not a tuple", self),
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
            _ => panic!("type {} is not an enum", self),
        }
    }

    /// Returns the spec type corresponding to this type. Panics if this type is not a
    /// spec type.
    pub fn to_spec_type(&self) -> &ASpecType {
        match self {
            AType::Spec(spec_type) => spec_type,
            _ => panic!("type {} is not a spec", self),
        }
    }

    /// Returns the generic type corresponding to this type. Panics if this type is not a
    /// generic type.
    pub fn to_generic_type(&self) -> &AGenericType {
        match self {
            AType::Generic(generic_type) => generic_type,
            _ => panic!("type {} is not a generic", self),
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

    /// Returns true if the type is generic.
    pub fn is_generic(&self) -> bool {
        matches!(self, AType::Generic(_))
    }

    /// Returns true if the type is `bool`.
    pub fn is_bool(&self) -> bool {
        matches!(self, AType::Bool)
    }

    /// Returns generic parameters defined for this type.
    pub fn params(&self) -> Option<&AParams> {
        match self {
            AType::Function(fn_sig) => fn_sig.params.as_ref(),
            AType::Struct(struct_type) => struct_type.maybe_params.as_ref(),
            AType::Enum(enum_type) => enum_type.maybe_params.as_ref(),
            AType::Spec(spec_type) => spec_type.maybe_params.as_ref(),
            _ => None,
        }
    }
}

/// Returns the size of the given type in bytes on the target system (includes padding).
pub fn size_of_type(ctx: &ProgramContext, type_key: TypeKey) -> u64 {
    let ll_ctx = Context::create();
    let converter = TypeConverter::new(
        &ll_ctx,
        &ctx.type_store,
        &ctx.type_monomorphizations,
        &ctx.config.target_machine,
    );
    converter.size_of_type(type_key)
}
