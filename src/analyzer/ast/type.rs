use std::fmt;
use std::fmt::{Display, Formatter};

use crate::analyzer::ast::array::AArrayType;
use crate::analyzer::ast::func::AFnSig;
use crate::analyzer::ast::generic::AGenericType;
use crate::analyzer::ast::params::AParams;
use crate::analyzer::ast::pointer::APointerType;
use crate::analyzer::ast::r#enum::AEnumType;
use crate::analyzer::ast::r#struct::AStructType;
use crate::analyzer::ast::spec::ASpecType;
use crate::analyzer::ast::tuple::ATupleType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::unresolved::UnresolvedType;

#[derive(Debug, Clone, PartialEq)]
pub enum AType {
    // Primitive types.
    Bool,
    U8,
    I8,
    U32,
    I32,
    F32,
    I64,
    U64,
    F64,
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
            AType::U8 => write!(f, "u8"),
            AType::I8 => write!(f, "i8"),
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
    /// Analyzes `typ` and returns an analyzed version of it.
    pub fn from(ctx: &mut ProgramContext, typ: &Type) -> AType {
        match typ {
            Type::Unresolved(unresolved_type) => {
                return AType::from_unresolved(ctx, unresolved_type);
            }

            Type::Function(sig) => AType::from_fn_sig(AFnSig::from(ctx, &*sig)),

            Type::Tuple(tuple_type) => {
                let a_tuple_type = ATupleType::from(ctx, tuple_type);
                return AType::Tuple(a_tuple_type);
            }

            Type::Array(array_type) => {
                let a_array_type = AArrayType::from(ctx, array_type);
                return AType::Array(a_array_type);
            }

            Type::Pointer(ptr_type) => {
                let a_ptr_type = APointerType::from(ctx, ptr_type);
                if a_ptr_type.pointee_type_key == ctx.unknown_type_key() {
                    return AType::Unknown("<unknown>".to_string());
                }

                return AType::Pointer(a_ptr_type);
            }
        }
    }

    /// Tries to analyze/resolve the unresolved type.
    fn from_unresolved(ctx: &mut ProgramContext, unresolved_type: &UnresolvedType) -> AType {
        let maybe_mod_name = unresolved_type.maybe_mod_name.as_ref();
        let type_name = unresolved_type.name.as_str();

        // Return early if the mod name is invalid.
        if let Some(mod_name) = maybe_mod_name {
            if !ctx.check_mod_name(mod_name, unresolved_type) {
                return AType::Unknown("<unknown>".to_string());
            }
        }

        // Check if the type has already been marked as invalid. If so, we should avoid
        // trying to resolve it and simply return the unknown type.
        if ctx.is_name_of_invalid_type(type_name) {
            return AType::Unknown(type_name.to_string());
        }

        // Check if this is a generic type parameter.
        if let Some(param) = ctx.get_param(type_name) {
            return AType::Generic(
                ctx.must_get_type(param.generic_type_key)
                    .to_generic_type()
                    .clone(),
            );
        }

        // If the type has already been analyzed, just return it.
        if let Some(struct_type) = ctx.get_struct_type(maybe_mod_name, type_name) {
            return AType::Struct(struct_type.clone());
        }
        if let Some(enum_type) = ctx.get_enum_type(maybe_mod_name, type_name) {
            return AType::Enum(enum_type.clone());
        }
        if let Some(spec_type) = ctx.get_spec_type(maybe_mod_name, type_name) {
            return AType::Spec(spec_type.clone());
        }
        if let Some(fn_sig) = ctx.get_defined_fn_sig(maybe_mod_name, type_name) {
            return AType::from_fn_sig(fn_sig.clone());
        }
        if let Some(fn_type) = ctx.get_fn(maybe_mod_name, type_name) {
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
            format_code!("type {} is not defined", unresolved_type).as_str(),
            unresolved_type,
        ));

        return AType::Unknown("<unknown>".to_string());
    }

    /// Returns the mapping from parsed type to analyzed type for all primitives types.
    pub fn primitives() -> Vec<AType> {
        vec![
            AType::Bool,
            AType::U8,
            AType::I8,
            AType::U32,
            AType::I32,
            AType::F32,
            AType::I64,
            AType::U64,
            AType::F64,
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
            AType::F32 => "f32",
            AType::I64 => "i64",
            AType::U64 => "u64",
            AType::F64 => "f64",
            AType::Int => "int",
            AType::Uint => "uint",
            AType::Str => "str",
            AType::Struct(t) => t.name.as_str(),
            AType::Enum(t) => t.name.as_str(),
            AType::Spec(t) => t.name.as_str(),
            AType::Tuple(_) | AType::Pointer(_) | AType::Array(_) => "",
            AType::Function(t) => t.name.as_str(),
            AType::Generic(g) => g.name.as_str(),
            AType::Unknown(name) => name.as_str(),
        }
    }

    /// Returns the type's mangled name, if it has one.
    pub fn maybe_mangled_name(&self) -> Option<&String> {
        match self {
            AType::Function(fn_sig) => Some(&fn_sig.mangled_name),
            AType::Struct(struct_type) => Some(&struct_type.mangled_name),
            AType::Enum(enum_type) => Some(&enum_type.mangled_name),
            _ => None,
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
            (a, b) => {
                let a = match ctx.get_cur_self_type_key() {
                    Some(tk) if a.is_unknown() && a.name() == "Self" => ctx.must_get_type(tk),
                    _ => a,
                };

                let b = match ctx.get_cur_self_type_key() {
                    Some(tk) if b.is_unknown() && b.name() == "Self" => ctx.must_get_type(tk),
                    _ => b,
                };

                a == b
            }
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
            | AType::F32
            | AType::I64
            | AType::U64
            | AType::F64
            | AType::Int
            | AType::Uint
            | AType::Str
            | AType::Function(_)
            | AType::Pointer(_)
            | AType::Generic(_)
            | AType::Spec(_)
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
        // TODO: Return false if the type implements auto-copy.
        self.is_composite() || self.is_generic()
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
                | AType::U32
                | AType::I32
                | AType::U64
                | AType::I64
                | AType::Int
                | AType::Uint
        )
    }

    /// Returns true if this is a pointer type.
    pub fn is_ptr(&self) -> bool {
        matches!(self, AType::Pointer(_))
    }

    /// Returns true if this is a mutating pointer type.
    pub fn is_mut_pointer(&self) -> bool {
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

    /// Returns true if the type is primitive.
    pub fn is_primitive(&self) -> bool {
        matches!(
            self,
            AType::Bool
                | AType::U8
                | AType::I8
                | AType::U32
                | AType::I32
                | AType::F32
                | AType::I64
                | AType::U64
                | AType::F64
                | AType::Int
                | AType::Uint
                | AType::Str
        )
    }

    /// Returns true if arithmetic operations on this type should be signed. Otherwise, this type
    /// either doesn't support arithmetic operations, or requires unsigned operations.
    pub fn is_signed(&self) -> bool {
        match self {
            AType::I8 | AType::I32 | AType::F32 | AType::I64 | AType::F64 | AType::Int => true,
            AType::Bool
            | AType::Str
            | AType::U8
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

    /// Returns a string containing a human-readable version of the type.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        match self {
            AType::Bool
            | AType::Str
            | AType::I8
            | AType::U8
            | AType::U32
            | AType::I32
            | AType::F32
            | AType::I64
            | AType::U64
            | AType::F64
            | AType::Int
            | AType::Uint => {
                format!("{}", self)
            }
            AType::Struct(s) => format!("{}", s.display(ctx)),
            AType::Enum(e) => format!("{}", e.display(ctx)),
            AType::Spec(s) => s.name.clone(),
            AType::Tuple(t) => format!("{}", t.display(ctx)),
            AType::Array(a) => format!("{}", a.display(ctx)),
            AType::Function(func) => format!("{}", func.display(ctx)),
            AType::Pointer(t) => format!("{}", t.display(ctx)),
            AType::Generic(t) => t.name.clone(),
            AType::Unknown(name) => format!("{}", name),
        }
    }

    /// Returns generic parameters defined for this type.
    pub fn params(&self) -> Option<&AParams> {
        match self {
            AType::Function(fn_sig) => fn_sig.params.as_ref(),
            AType::Struct(struct_type) => struct_type.maybe_params.as_ref(),
            AType::Enum(enum_type) => enum_type.maybe_params.as_ref(),
            _ => None,
        }
    }
}
