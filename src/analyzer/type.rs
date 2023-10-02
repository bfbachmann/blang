use core::fmt;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::hash::Hash;

use colored::*;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func_sig::RichFnSig;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#struct::RichStructType;
use crate::analyzer::tuple::RichTupleType;
use crate::parser::r#type::Type;
use crate::parser::unresolved::UnresolvedType;
use crate::{format_code, util};

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

    /// Returns the type ID for the `bool` type.
    pub fn bool() -> Self {
        TypeId { typ: Type::bool() }
    }

    /// Returns the type ID for the `i64` type.
    pub fn i64() -> Self {
        TypeId { typ: Type::i64() }
    }

    /// Returns the type ID for the `unsafeptr` type.
    pub fn unsafeptr() -> Self {
        TypeId {
            typ: Type::unsafeptr(),
        }
    }

    /// Returns the type ID for the `usize` type.
    pub fn usize() -> Self {
        TypeId { typ: Type::usize() }
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
    UnsafePtr,
    /// Represents a pointer-sized unsigned integer.
    USize,
    Struct(RichStructType),
    Tuple(RichTupleType),
    Function(Box<RichFnSig>),
    /// Represents a type that did not pass semantic analysis and thus was never properly resolved.
    Unknown(String),
}

impl Display for RichType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            RichType::Bool => write!(f, "bool"),
            RichType::Str => write!(f, "str"),
            RichType::I64 => write!(f, "i64"),
            RichType::USize => write!(f, "usize"),
            RichType::UnsafePtr => write!(f, "unsafeptr"),
            RichType::Struct(s) => write!(f, "{}", s),
            RichType::Tuple(t) => write!(f, "{}", t),
            RichType::Function(func) => write!(f, "{}", func),
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
            | (RichType::UnsafePtr, RichType::UnsafePtr)
            | (RichType::USize, RichType::USize) => true,
            (RichType::Struct(s1), RichType::Struct(s2)) => s1 == s2,
            (RichType::Tuple(t1), RichType::Tuple(t2)) => t1 == t2,
            (RichType::Function(f1), RichType::Function(f2)) => *f1 == *f2,
            (_, _) => false,
        }
    }
}

impl RichType {
    /// Analyzes and resolves the given type (if unresolved), stores the resolved type in the
    /// program context, and returns its type ID.
    pub fn analyze(ctx: &mut ProgramContext, typ: &Type) -> TypeId {
        // If the type is `This`, just return the type ID that corresponds to the current `impl`
        // block.
        if let Type::This(this_type) = typ {
            return match ctx.get_impl_type_id() {
                Some(type_id) => type_id.clone(),
                None => {
                    ctx.add_err(AnalyzeError::new(
                        ErrorKind::TypeNotDefined,
                        format_code!("type {} is not defined", this_type.name).as_str(),
                        this_type,
                    ));

                    TypeId::unknown()
                }
            };
        }

        // Check if the type has already been resolved and, if so, just return its ID.
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

                // Check if the type has already been marked as invalid. If so, we should avoid
                // trying to resolve it and simply return the ID of the unknown type.
                if ctx.get_invalid_type(type_name).is_some() {
                    return RichType::Unknown(type_name.to_string());
                }

                // If the type has already been analyzed, just return it.
                if let Some(rich_struct_type) = ctx.get_struct(type_name) {
                    return RichType::Struct(rich_struct_type.clone());
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

                ctx.add_err(AnalyzeError::new(
                    ErrorKind::TypeNotDefined,
                    format_code!("type {} is not defined", type_name).as_str(),
                    unresolved_type,
                ));

                return RichType::Unknown("<unknown>".to_string());
            }

            Type::This(_) => {
                unreachable!()
            }

            Type::I64(_) => RichType::I64,

            Type::UnsafePtr(_) => RichType::UnsafePtr,

            Type::USize(_) => RichType::USize,

            Type::Bool(_) => RichType::Bool,

            Type::Str(_) => RichType::Str,

            Type::Function(sig) => RichType::Function(Box::new(RichFnSig::from(ctx, &*sig))),

            Type::Struct(struct_type) => {
                let rich_struct_type = RichStructType::from(ctx, struct_type, true);
                return RichType::Struct(rich_struct_type);
            }

            Type::Tuple(tuple_type) => {
                let rich_tuple_type = RichTupleType::from(ctx, tuple_type);
                return RichType::Tuple(rich_tuple_type);
            }
        }
    }

    /// Creates a new rich function type from the given signature.
    pub fn from_fn_sig(sig: RichFnSig) -> Self {
        RichType::Function(Box::new(sig))
    }

    /// Returns a mapping from primitive type ID to analyzed primitive type.
    pub fn primitives() -> HashMap<TypeId, RichType> {
        // TODO: make this static?
        HashMap::from([
            (TypeId::bool(), RichType::Bool),
            (TypeId::i64(), RichType::I64),
            (TypeId::str(), RichType::Str),
            (TypeId::unsafeptr(), RichType::UnsafePtr),
            (TypeId::usize(), RichType::USize),
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
    pub fn same_as(&self, other: &RichType) -> bool {
        match (self, other) {
            (RichType::Function(f1), RichType::Function(f2)) => {
                if f1.args.len() != f2.args.len() {
                    return false;
                }

                for (a, b) in f1.args.iter().zip(f2.args.iter()) {
                    if a.type_id != b.type_id {
                        return false;
                    }
                }

                util::optionals_are_equal(&f1.ret_type_id, &f2.ret_type_id)
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
        if self.get_type_hierarchy(ctx, typ, &mut hierarchy) {
            Some(hierarchy)
        } else {
            None
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
            | RichType::UnsafePtr
            | RichType::USize
            | RichType::Str
            | RichType::Function(_)
            | RichType::Unknown(_) => false,
            RichType::Struct(s) => {
                for field in &s.fields {
                    let field_type = ctx.get_resolved_type(&field.type_id).unwrap();
                    if field_type == typ {
                        hierarchy.push(field_type);
                        return true;
                    } else if field_type.get_type_hierarchy(ctx, typ, hierarchy) {
                        return true;
                    }
                }

                false
            }
            RichType::Tuple(t) => {
                for type_id in &t.type_ids {
                    let field_type = ctx.get_resolved_type(type_id).unwrap();
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
            RichType::Bool | RichType::I64 | RichType::Function(_) => false,
            _ => true,
        }
    }

    /// Returns true if arithmetic operations on this type should be signed. Otherwise, this type
    /// either doesn't support arithmetic operations, or requires unsigned operations.
    pub fn is_signed(&self) -> bool {
        match self {
            RichType::I64 => true,
            RichType::Bool
            | RichType::Str
            | RichType::UnsafePtr
            | RichType::USize
            | RichType::Struct(_)
            | RichType::Tuple(_)
            | RichType::Function(_)
            | RichType::Unknown(_) => false,
        }
    }

    /// Returns the size of this type (i.e. the amount of memory required to store it) in bytes.
    pub fn size_bytes(&self, ctx: &ProgramContext) -> u64 {
        match self {
            RichType::Bool => 1,

            RichType::I64
            | RichType::UnsafePtr
            | RichType::USize
            | RichType::Function(_)
            | RichType::Str => 8,

            RichType::Struct(struct_type) => {
                let mut size = 0;
                for field in &struct_type.fields {
                    let field_type = ctx.get_resolved_type(&field.type_id).unwrap();
                    size += field_type.size_bytes(ctx);
                }

                size
            }

            RichType::Tuple(tuple_type) => {
                let mut size = 0;
                for type_id in &tuple_type.type_ids {
                    let field_type = ctx.get_resolved_type(&type_id).unwrap();
                    size += field_type.size_bytes(ctx)
                }

                size
            }

            RichType::Unknown(_) => 0,
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
            }))
        )
    }
}
