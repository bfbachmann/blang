use core::fmt;
use std::cmp::max;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::hash::Hash;

use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, AnalyzeResult, ErrorKind};
use crate::analyzer::func_sig::RichFnSig;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#enum::{check_enum_containment_cycles, RichEnumType};
use crate::analyzer::r#struct::{check_struct_containment_cycles, RichStructType};
use crate::analyzer::spec::RichSpec;
use crate::analyzer::tmpl_params::RichTmplParam;
use crate::analyzer::tuple::{check_tuple_containment_cycles, RichTupleType};
use crate::format_code;
use crate::parser::r#type::Type;
use crate::parser::unresolved::UnresolvedType;

/// Represents a unique identifier for a type that can be used to look up the corresponding
/// fully-resolved type. Under the hood, a type ID is really just a parsed type without any
/// information from type resolution/analysis. Every parsed type should map to exactly one resolved
/// (or invalid) type, but many parsed types may map to the same resolved type.
#[derive(Clone, Hash, Debug, PartialEq, Eq)]
pub struct TypeId {
    typ: Type,
}

impl Display for TypeId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.typ)
    }
}

impl TypeId {
    /// Creates a new type ID from the given parsed type.
    pub fn from(typ: Type) -> Self {
        TypeId { typ }
    }

    /// Returns the type ID corresponding to the type with the given name.
    pub fn from_name(name: &str) -> Self {
        match name {
            "bool" => TypeId::bool(),
            "i64" => TypeId::i64(),
            "u64" => TypeId::u64(),
            "ptr" => TypeId::ptr(),
            "str" => TypeId::str(),
            _ => TypeId::new_unresolved(name),
        }
    }

    /// Creates a new type ID that would correspond to the unresolved type with the given name.
    pub fn new_unresolved(type_name: &str) -> Self {
        TypeId::from(Type::new_unknown(type_name))
    }

    /// Returns the type ID for the `bool` type.
    pub fn bool() -> Self {
        TypeId { typ: Type::bool() }
    }

    /// Returns the type ID for the `i64` type.
    pub fn i64() -> Self {
        TypeId { typ: Type::i64() }
    }

    /// Returns the type ID for the `ptr` type.
    pub fn ptr() -> Self {
        TypeId { typ: Type::ptr() }
    }

    /// Returns the type ID for the `u64` type.
    pub fn u64() -> Self {
        TypeId { typ: Type::u64() }
    }

    /// Returns the type ID for the `str` type.
    pub fn str() -> Self {
        TypeId { typ: Type::str() }
    }

    /// Returns the type ID for the `<unknown>` type.
    pub fn unknown() -> Self {
        TypeId {
            typ: Type::Unresolved(UnresolvedType::unknown()),
        }
    }

    /// Returns the type ID for the `<none>` type (that is, the absence of a type).
    pub fn none() -> Self {
        TypeId {
            typ: Type::Unresolved(UnresolvedType::none()),
        }
    }

    /// Returns true if this type ID corresponds to the `bool` type and false otherwise.
    pub fn is_bool(&self) -> bool {
        matches!(self.typ, Type::Bool(_))
    }

    /// Returns the parsed type associated with this type ID.
    pub fn typ(&self) -> &Type {
        &self.typ
    }
}

/// Represents a semantically valid and fully resolved type.
#[derive(Clone, Debug)]
pub enum RichType {
    Bool,
    Str,
    I64,
    /// These are pointers that are not garbage collected and allow pointer arithmetic.
    /// This type translates directly to `void *` in C.
    Ptr,
    /// Represents a pointer-sized unsigned integer.
    U64,
    Struct(RichStructType),
    Enum(RichEnumType),
    Tuple(RichTupleType),
    Function(Box<RichFnSig>),
    /// A templated (generic) type parameter.
    Templated(RichTmplParam),
    /// Represents a type that did not pass semantic analysis and thus was never properly resolved.
    Unknown(String),
}

impl Display for RichType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            RichType::Bool => write!(f, "bool"),
            RichType::Str => write!(f, "str"),
            RichType::I64 => write!(f, "i64"),
            RichType::U64 => write!(f, "u64"),
            RichType::Ptr => write!(f, "ptr"),
            RichType::Struct(s) => write!(f, "{}", s),
            RichType::Enum(e) => write!(f, "{}", e),
            RichType::Tuple(t) => write!(f, "{}", t),
            RichType::Function(func) => write!(f, "{}", func),
            RichType::Templated(param) => write!(f, "{}", param),
            RichType::Unknown(name) => write!(f, "{}", name),
        }
    }
}

impl PartialEq for RichType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (RichType::Bool, RichType::Bool)
            | (RichType::I64, RichType::I64)
            | (RichType::Str, RichType::Str)
            | (RichType::Ptr, RichType::Ptr)
            | (RichType::U64, RichType::U64) => true,
            (RichType::Struct(s1), RichType::Struct(s2)) => s1 == s2,
            (RichType::Enum(e1), RichType::Enum(e2)) => e1 == e2,
            (RichType::Tuple(t1), RichType::Tuple(t2)) => t1 == t2,
            (RichType::Function(f1), RichType::Function(f2)) => *f1 == *f2,
            (RichType::Templated(t1), RichType::Templated(t2)) => t1 == t2,
            (_, _) => false,
        }
    }
}

impl RichType {
    /// Analyzes and resolves the given type (if unresolved), stores the resolved type in the
    /// program context, and returns its type ID.
    pub fn analyze(ctx: &mut ProgramContext, typ: &Type) -> TypeId {
        // If the type is `This`, just return it. It will be substituted for an actual type later.
        if let Type::This(this_type) = typ {
            return match ctx.get_this_type_id() {
                Some(type_id) => type_id.clone(),
                None => {
                    ctx.add_err(AnalyzeError::new(
                        ErrorKind::UndefType,
                        format_code!("type {} is not defined in this scope", this_type.name)
                            .as_str(),
                        this_type,
                    ));

                    TypeId::unknown()
                }
            };
        }

        // Check if the type has already been resolved and, if so, just return its ID as long as
        // it's not a template param type (because template params might need to be replaced).
        let id = TypeId::from(typ.clone());
        if ctx.get_resolved_type(&id).is_some() {
            return id;
        }

        // The type has not yet been resolved, so we'll try to resolve it and add the result to
        // the program context so it can be looked up using the type ID later.
        let resolved = RichType::resolve(ctx, typ);
        ctx.add_resolved_type(id.clone(), resolved);
        id
    }

    /// Attempts to recursively resolve the given parsed type.
    fn resolve(ctx: &mut ProgramContext, typ: &Type) -> RichType {
        match typ {
            Type::Unresolved(unresolved_type) => {
                let type_name = unresolved_type.name.as_str();

                // Check if the type is a primitive.
                if let Some(typ) = RichType::primitives().get(&TypeId::from(typ.clone())) {
                    return typ.clone();
                }

                // Check if the type has already been marked as invalid. If so, we should avoid
                // trying to resolve it and simply return the ID of the unknown type.
                if ctx.get_invalid_type(type_name).is_some() {
                    return RichType::Unknown(type_name.to_string());
                }

                // If the type has already been analyzed, just return it.
                if let Some(rich_struct_type) = ctx.get_struct(type_name) {
                    return RichType::Struct(rich_struct_type.clone());
                }
                if let Some(rich_enum_type) = ctx.get_enum(type_name) {
                    return RichType::Enum(rich_enum_type.clone());
                }
                if let Some(fn_sig) = ctx.get_extern_fn(type_name) {
                    return RichType::Function(Box::new(fn_sig.clone()));
                }
                if let Some(fn_type) = ctx.get_fn(type_name) {
                    return RichType::Function(Box::new(fn_type.signature.clone()));
                }

                // The type has not yet been analyzed, so make sure the type has at least been
                // declared somewhere and analyze it.
                if let Some(struct_type) = ctx.get_extern_struct(type_name) {
                    let rich_struct_type = RichStructType::from(ctx, &struct_type.clone(), false);
                    return RichType::Struct(rich_struct_type);
                }
                if let Some(enum_type) = ctx.get_extern_enum(type_name) {
                    let rich_enum_type = RichEnumType::from(ctx, &enum_type.clone());
                    return RichType::Enum(rich_enum_type);
                }

                ctx.add_err(AnalyzeError::new(
                    ErrorKind::UndefType,
                    format_code!("type {} is not defined", type_name).as_str(),
                    unresolved_type,
                ));

                return RichType::Unknown("<unknown>".to_string());
            }

            Type::This(_) => {
                unreachable!()
            }

            Type::I64(_) => RichType::I64,

            Type::Ptr(_) => RichType::Ptr,

            Type::U64(_) => RichType::U64,

            Type::Bool(_) => RichType::Bool,

            Type::Str(_) => RichType::Str,

            Type::Function(sig) => RichType::Function(Box::new(RichFnSig::from(ctx, &*sig))),

            Type::Struct(struct_type) => {
                let rich_struct_type = RichStructType::from(ctx, struct_type, true);
                return RichType::Struct(rich_struct_type);
            }

            Type::Enum(enum_type) => {
                let rich_enum_type = RichEnumType::from(ctx, enum_type);
                return RichType::Enum(rich_enum_type);
            }

            Type::Tuple(tuple_type) => {
                let rich_tuple_type = RichTupleType::from(ctx, tuple_type);
                return RichType::Tuple(rich_tuple_type);
            }
        }
    }

    /// Returns the type name.
    pub fn name(&self) -> String {
        match self {
            RichType::Bool => "bool".to_string(),
            RichType::Str => "str".to_string(),
            RichType::I64 => "i64".to_string(),
            RichType::Ptr => "ptr".to_string(),
            RichType::U64 => "u64".to_string(),
            RichType::Struct(s) => s.name.clone(),
            RichType::Enum(e) => e.name.clone(),
            RichType::Tuple(_) => "tuple".to_string(),
            RichType::Function(f) => f.name.clone(),
            RichType::Templated(t) => t.name.clone(),
            RichType::Unknown(_) => "<unknown>".to_string(),
        }
    }

    /// Creates a new rich function type from the given signature.
    pub fn from_fn_sig(sig: RichFnSig) -> Self {
        RichType::Function(Box::new(sig))
    }

    /// Returns the primitive type with the given name, if one exists.
    pub fn get_primitive(name: &str) -> Option<RichType> {
        match name {
            "bool" => Some(RichType::Bool),
            "i64" => Some(RichType::I64),
            "u64" => Some(RichType::U64),
            "str" => Some(RichType::Str),
            "ptr" => Some(RichType::Ptr),
            _ => None,
        }
    }

    /// Returns true if this is a numeric type.
    pub fn is_numeric(&self) -> bool {
        matches!(self, RichType::I64 | RichType::U64)
    }

    /// Returns a mapping from primitive type ID to analyzed primitive type.
    pub fn primitives() -> HashMap<TypeId, RichType> {
        // TODO: make this static?
        HashMap::from([
            (TypeId::bool(), RichType::Bool),
            (TypeId::i64(), RichType::I64),
            (TypeId::str(), RichType::Str),
            (TypeId::ptr(), RichType::Ptr),
            (TypeId::u64(), RichType::U64),
            (
                TypeId::unknown(),
                RichType::Unknown("<unknown>".to_string()),
            ),
            (TypeId::none(), RichType::Unknown("<none>".to_string())),
        ])
    }

    /// Returns true if this type is unknown.
    pub fn is_unknown(&self) -> bool {
        matches!(self, RichType::Unknown(_))
    }

    /// Returns true if the two types are the same.
    ///  - For primitive types (i64, bool, etc), they must be exactly the same type.
    ///  - For struct types, they must be exactly the same type.
    ///  - For function types, they must have arguments of the same type in the same order and the
    ///    same return types.
    ///
    /// `remapped_type_ids` will be used to replace type IDs in `other` before comparisons are
    /// performed.
    pub fn is_same_as(
        &self,
        other: &RichType,
        remapped_type_ids: &HashMap<TypeId, TypeId>,
    ) -> bool {
        match (self, other) {
            (RichType::Function(f1), RichType::Function(f2)) => {
                f1.is_same_as(f2, remapped_type_ids)
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
        typ: &RichType,
    ) -> Option<Vec<&RichType>> {
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
        typ: &RichType,
        hierarchy: &mut Vec<&'a RichType>,
    ) -> bool {
        hierarchy.push(&self);

        return match self {
            RichType::Bool
            | RichType::I64
            | RichType::Ptr
            | RichType::U64
            | RichType::Str
            | RichType::Function(_)
            | RichType::Templated(_)
            | RichType::Unknown(_) => false,

            RichType::Struct(s) => {
                for field in &s.fields {
                    let field_type = ctx.must_get_resolved_type(&field.type_id);
                    if field_type == typ {
                        hierarchy.push(field_type);
                        return true;
                    } else if field_type.get_type_hierarchy(ctx, typ, hierarchy) {
                        return true;
                    }
                }

                false
            }

            RichType::Enum(e) => {
                for variant in e.variants.values() {
                    if let Some(type_id) = &variant.maybe_type_id {
                        let variant_type = ctx.must_get_resolved_type(type_id);
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

            RichType::Tuple(t) => {
                for type_id in &t.type_ids {
                    let field_type = ctx.must_get_resolved_type(type_id);
                    if field_type == typ {
                        hierarchy.push(field_type);
                        return true;
                    } else if field_type.get_type_hierarchy(ctx, typ, hierarchy) {
                        return true;
                    }
                }

                false
            }
        };
    }

    /// Returns true only if this type is moved on assignment or when passed as an argument.
    pub fn requires_move(&self) -> bool {
        match self {
            RichType::Enum(_) | RichType::Struct(_) | RichType::Tuple(_) => true,
            _ => false,
        }
    }

    /// Returns true if arithmetic operations on this type should be signed. Otherwise, this type
    /// either doesn't support arithmetic operations, or requires unsigned operations.
    pub fn is_signed(&self) -> bool {
        match self {
            RichType::I64 => true,
            RichType::Bool
            | RichType::Str
            | RichType::Ptr
            | RichType::U64
            | RichType::Struct(_)
            | RichType::Enum(_)
            | RichType::Tuple(_)
            | RichType::Function(_)
            | RichType::Templated(_)
            | RichType::Unknown(_) => false,
        }
    }

    /// Returns the size of this type (i.e. the amount of memory required to store it) in bytes.
    pub fn size_bytes(&self, ctx: &ProgramContext) -> u32 {
        match self {
            // Bools are 1 byte.
            RichType::Bool => 1,

            // All of the following types are 64 bits (8 bytes).
            RichType::I64
            | RichType::Ptr
            | RichType::U64
            | RichType::Function(_)
            | RichType::Str => 8,

            // The size of a struct type is the sum of the sizes of all of its fields.
            RichType::Struct(struct_type) => {
                let mut size = 0;
                for field in &struct_type.fields {
                    let field_type = ctx.must_get_resolved_type(&field.type_id);
                    size += field_type.size_bytes(ctx);
                }

                size
            }

            // The size of an enum type is 1 byte (to hold the variant number) plus the greatest
            // size of all of its variants.
            RichType::Enum(enum_type) => {
                let mut size = 0;
                for variant in enum_type.variants.values() {
                    if let Some(type_id) = &variant.maybe_type_id {
                        let variant_type = ctx.must_get_resolved_type(type_id);
                        size = max(size, variant_type.size_bytes(ctx));
                    }
                }

                size + 1
            }

            RichType::Tuple(tuple_type) => {
                let mut size = 0;
                for type_id in &tuple_type.type_ids {
                    let field_type = ctx.must_get_resolved_type(&type_id);
                    size += field_type.size_bytes(ctx)
                }

                size
            }

            RichType::Unknown(_) => 0,

            RichType::Templated(_) => panic!("templated types are not sized"),
        }
    }

    /// Returns the function signature corresponding to this type. Panics if this type is not a
    /// function type.
    pub fn to_fn_sig(&self) -> &RichFnSig {
        match self {
            RichType::Function(fn_sig) => fn_sig,
            _ => panic!("type {} is not a function", self),
        }
    }

    /// Returns the struct type corresponding to this type. Panics if this type is not a
    /// struct type.
    pub fn to_struct_type(&self) -> &RichStructType {
        match self {
            RichType::Struct(struct_type) => struct_type,
            _ => panic!("type {} is not a struct", self),
        }
    }

    /// Returns true if this is a composite type (i.e. a type that can contain other types).
    pub fn is_composite(&self) -> bool {
        matches!(
            self,
            RichType::Struct(_) | RichType::Enum(_) | RichType::Tuple(_)
        )
    }
}

/// Analyzes type containment and returns an error if there are any illegal type containment cycles
/// that would result in infinite-sized types.
pub fn check_type_containment(
    ctx: &ProgramContext,
    typ: &Type,
    hierarchy: &mut Vec<String>,
) -> AnalyzeResult<()> {
    match typ {
        Type::Unresolved(unresolved_type) => {
            if let Some(struct_type) = ctx.get_extern_struct(unresolved_type.name.as_str()) {
                check_struct_containment_cycles(ctx, struct_type, hierarchy)?;
            } else if let Some(enum_type) = ctx.get_extern_enum(unresolved_type.name.as_str()) {
                check_enum_containment_cycles(ctx, enum_type, hierarchy)?;
            }
        }

        Type::Struct(field_struct_type) => {
            check_struct_containment_cycles(ctx, field_struct_type, hierarchy)?;
        }

        Type::Enum(field_enum_type) => {
            check_enum_containment_cycles(ctx, field_enum_type, hierarchy)?;
        }

        Type::Tuple(field_tuple_type) => {
            check_tuple_containment_cycles(ctx, field_tuple_type, hierarchy)?;
        }

        Type::This(_) => {
            // This should never happen because struct types declared at the top-level of
            // the program cannot reference type `This` because they're not in an `impl`.
            unreachable!();
        }

        // These types can't have containment cycles.
        Type::I64(_)
        | Type::Str(_)
        | Type::Bool(_)
        | Type::Function(_)
        | Type::Ptr(_)
        | Type::U64(_) => {}
    }

    Ok(())
}

/// Checks whether the type corresponding to the given ID satisfies the given spec and returns an
/// error if it doesn't.
pub fn check_type_satisfies_spec(
    ctx: &ProgramContext,
    type_id: &TypeId,
    spec: &RichSpec,
) -> Result<(), String> {
    let member_fns = HashMap::new();
    let member_fns = match ctx.get_type_member_fns(type_id) {
        Some(mem_fns) => mem_fns,
        None => &member_fns,
    };

    for spec_fn_sig in &spec.fn_sigs {
        match member_fns.get(spec_fn_sig.name.as_str()) {
            Some(fn_sig) => {
                // Create a mapping from the spec type ID to the given type. This mapping will be
                // used to replace instances of the spec type ID in the function signature when
                // checking that the function signatures match.
                let remapped_type_ids = HashMap::from([(spec.type_id(), type_id.clone())]);
                if !fn_sig.is_same_as(spec_fn_sig, &remapped_type_ids) {
                    return Err(format_code!(
                        "Function {} on type {} doesn't match function {} on spec {}.",
                        fn_sig,
                        type_id,
                        spec_fn_sig,
                        spec.name
                    )
                    .to_string());
                }
            }
            None => {
                return Err(format_code!(
                    "Type {} is missing function {} from spec {}.",
                    type_id,
                    spec_fn_sig,
                    spec.name,
                )
                .to_string())
            }
        };
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::analyzer::arg::RichArg;
    use crate::analyzer::func_sig::RichFnSig;
    use crate::analyzer::r#struct::{RichField, RichStructType};
    use crate::analyzer::r#type::{RichType, TypeId};
    use crate::parser::arg::Argument;
    use crate::parser::func_sig::FunctionSignature;
    use crate::parser::r#type::Type;

    #[test]
    fn partial_eq() {
        assert_eq!(RichType::Bool, RichType::Bool);
        assert_eq!(RichType::Str, RichType::Str);
        assert_eq!(RichType::I64, RichType::I64);
        assert_eq!(RichType::U64, RichType::U64);
        assert_eq!(
            RichType::Struct(RichStructType {
                name: "asdf".to_string(),
                fields: vec![RichField {
                    name: "field".to_string(),
                    type_id: TypeId::bool(),
                }],
            }),
            RichType::Struct(RichStructType {
                name: "asdf".to_string(),
                fields: vec![RichField {
                    name: "field".to_string(),
                    type_id: TypeId::bool(),
                }],
            })
        );
        assert_eq!(
            RichType::Function(Box::new(RichFnSig {
                name: "test_func".to_string(),
                args: vec![RichArg {
                    name: "arg1".to_string(),
                    type_id: TypeId::bool(),
                    is_mut: false,
                }],
                ret_type_id: Some(TypeId::str()),
                type_id: TypeId::from(Type::Function(Box::new(
                    FunctionSignature::new_with_default_pos(
                        "test_func",
                        vec![Argument::new_with_default_pos("arg1", Type::bool(), false)],
                        Some(Type::str())
                    )
                ))),
                impl_type_id: None,
                tmpl_params: None,
            })),
            RichType::Function(Box::new(RichFnSig {
                name: "test_func".to_string(),
                args: vec![RichArg {
                    name: "arg1".to_string(),
                    type_id: TypeId::bool(),
                    is_mut: false,
                }],
                ret_type_id: Some(TypeId::str()),
                type_id: TypeId::from(Type::Function(Box::new(
                    FunctionSignature::new_with_default_pos(
                        "test_func",
                        vec![Argument::new_with_default_pos("arg1", Type::bool(), false)],
                        Some(Type::str())
                    )
                ))),
                impl_type_id: None,
                tmpl_params: None,
            }))
        )
    }
}
