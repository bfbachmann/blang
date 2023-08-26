use core::fmt;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::hash::Hash;

use colored::*;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::RichFnSig;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#struct::RichStructType;
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

    /// Returns the type ID for the `bool` type.
    pub fn bool() -> Self {
        TypeId { typ: Type::bool() }
    }

    /// Returns the type ID for the `i64` type.
    pub fn i64() -> Self {
        TypeId { typ: Type::i64() }
    }

    /// Returns the type ID for the `string` type.
    pub fn string() -> Self {
        TypeId {
            typ: Type::string(),
        }
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
}

/// Represents a semantically valid and fully resolved type.
#[derive(Clone, Debug)]
pub enum RichType {
    Bool,
    String,
    I64,
    Struct(RichStructType),
    Function(Box<RichFnSig>),
    /// Represents a type that did not pass semantic analysis and thus was never properly resolved.
    Unknown(String),
}

impl Display for RichType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            RichType::Bool => write!(f, "bool"),
            RichType::String => write!(f, "string"),
            RichType::I64 => write!(f, "i64"),
            RichType::Struct(s) => write!(f, "{}", s),
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
            | (RichType::String, RichType::String) => true,
            (RichType::Struct(s1), RichType::Struct(s2)) => s1 == s2,
            (RichType::Function(f1), RichType::Function(f2)) => *f1 == *f2,
            (_, _) => false,
        }
    }
}

impl RichType {
    /// Analyzes and resolves the given type (if unresolved), stores the resolved type in the
    /// program context, and returns its type ID.
    pub fn analyze(ctx: &mut ProgramContext, typ: &Type) -> TypeId {
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

                ctx.add_err(AnalyzeError::new_with_locatable(
                    ErrorKind::TypeNotDefined,
                    format_code!("type {} is not defined", type_name).as_str(),
                    Box::new(unresolved_type.clone()),
                ));

                return RichType::Unknown("<unknown>".to_string());
            }

            Type::I64(_) => RichType::I64,

            Type::Bool(_) => RichType::Bool,

            Type::String(_) => RichType::String,

            Type::Function(sig) => RichType::Function(Box::new(RichFnSig::from(ctx, &*sig))),

            Type::Struct(struct_type) => {
                let rich_struct_type = RichStructType::from(ctx, struct_type, true);
                return RichType::Struct(rich_struct_type);
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
            (TypeId::string(), RichType::String),
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
            | RichType::String
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
        };
    }
}

#[cfg(test)]
mod tests {
    use crate::analyzer::func::{RichArg, RichFnSig};
    use crate::analyzer::r#struct::{RichField, RichStructType};
    use crate::analyzer::r#type::{RichType, TypeId};
    use crate::parser::arg::Argument;
    use crate::parser::func_sig::FunctionSignature;
    use crate::parser::r#type::Type;

    #[test]
    fn partial_eq() {
        assert_eq!(RichType::Bool, RichType::Bool);
        assert_eq!(RichType::String, RichType::String);
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
                }],
                ret_type_id: Some(TypeId::string()),
                type_id: TypeId::from(Type::Function(Box::new(
                    FunctionSignature::new_with_default_pos(
                        "test_func",
                        vec![Argument::new("arg1", Type::bool())],
                        Some(Type::string())
                    )
                ))),
            })),
            RichType::Function(Box::new(RichFnSig {
                name: "test_func".to_string(),
                args: vec![RichArg {
                    name: "arg1".to_string(),
                    type_id: TypeId::bool(),
                }],
                ret_type_id: Some(TypeId::string()),
                type_id: TypeId::from(Type::Function(Box::new(
                    FunctionSignature::new_with_default_pos(
                        "test_func",
                        vec![Argument::new("arg1", Type::bool())],
                        Some(Type::string())
                    )
                ))),
            }))
        )
    }
}