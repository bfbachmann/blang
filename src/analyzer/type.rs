use core::fmt;
use std::fmt::Formatter;

use colored::*;

use crate::analyzer::error::AnalyzeResult;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::RichFnSig;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#struct::RichStruct;

use crate::parser::r#type::Type;

/// Represents a semantically valid and fully resolved type.
#[derive(Clone, Debug)]
pub enum RichType {
    Bool,
    String,
    I64,
    Struct(RichStruct),
    Function(Box<RichFnSig>),
    /// Represents a type that did not pass semantic analysis and thus was never properly resolved.
    Unknown(String),
}

impl fmt::Display for RichType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
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
    /// Analyzes and resolves the given type (if unresolved) and returns it. This will also store
    /// type information in the program context.
    pub fn from(ctx: &mut ProgramContext, typ: &Type) -> AnalyzeResult<Self> {
        return match typ {
            Type::Unresolved(unresolved_type) => {
                let type_name = unresolved_type.name.as_str();

                // Check if the type has already been marked as invalid. If so, we should avoid
                // trying to resolve it and simply return an unknown type.
                if ctx.get_invalid_type(type_name).is_some() {
                    return Ok(RichType::Unknown(type_name.to_string()));
                }

                // If the type has already been analyzed, just return it.
                if let Some(rich_struct_type) = ctx.get_struct(type_name) {
                    return Ok(RichType::Struct(rich_struct_type.clone()));
                }
                if let Some(fn_sig) = ctx.get_extern_fn(type_name) {
                    return Ok(RichType::Function(Box::new(fn_sig.clone())));
                }
                if let Some(fn_type) = ctx.get_fn(type_name) {
                    return Ok(RichType::Function(Box::new(fn_type.signature.clone())));
                }

                // The type has not yet been analyzed, so make sure the type has at least been
                // declared somewhere and analyze it.
                if let Some(struct_type) = ctx.get_extern_struct(type_name) {
                    let rich_struct_type = RichStruct::from(ctx, &struct_type.clone(), false)?;
                    return Ok(RichType::Struct(rich_struct_type));
                }

                ctx.add_err(AnalyzeError::new_with_locatable(
                    ErrorKind::TypeNotDefined,
                    format!("type `{}` is not defined", type_name.blue()).as_str(),
                    Box::new(unresolved_type.clone()),
                ));

                return Ok(RichType::Unknown("<unknown>".to_string()));
            }

            Type::I64(_) => Ok(RichType::I64),

            Type::Bool(_) => Ok(RichType::Bool),

            Type::String(_) => Ok(RichType::String),

            Type::Function(sig) => Ok(RichType::Function(Box::new(RichFnSig::from(ctx, &*sig)?))),

            Type::Struct(struct_type) => {
                let rich_struct_type = RichStruct::from(ctx, struct_type, true)?;
                return Ok(RichType::Struct(rich_struct_type));
            }
        };
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
    pub fn contains_type(&self, typ: &RichType) -> Option<Vec<&RichType>> {
        let mut hierarchy = vec![];
        if self.get_type_hierarchy(typ, &mut hierarchy) {
            Some(hierarchy)
        } else {
            None
        }
    }

    /// Returns true if this type contains the given type. If true, the given `hierarchy` Vec will
    /// be filled with the hierarchy from `self` to `typ`.
    fn get_type_hierarchy<'a>(&'a self, typ: &RichType, hierarchy: &mut Vec<&'a RichType>) -> bool {
        hierarchy.push(&self);

        return match self {
            RichType::Bool
            | RichType::I64
            | RichType::String
            | RichType::Function(_)
            | RichType::Unknown(_) => false,
            RichType::Struct(s) => {
                for field in &s.fields {
                    if &field.typ == typ {
                        hierarchy.push(&field.typ);
                        return true;
                    } else if field.typ.get_type_hierarchy(typ, hierarchy) {
                        return true;
                    }
                }

                false
            }
        };
    }

    /// Formats the given type hierarchy like this
    ///
    ///     `A` -> `B` -> `C`
    pub fn hierarchy_to_string(hierarchy: Vec<String>) -> String {
        let mut s = String::from("");
        for (i, type_name) in hierarchy.iter().enumerate() {
            if i == 0 {
                s.push_str(format!("`{}`", type_name).blue().to_string().as_str());
            } else {
                s.push_str(format!(" -> `{}`", type_name).blue().to_string().as_str())
            }
        }

        s.to_string()
    }

    /// Returns true if both types are compatible (i.e. they have the same representation in
    /// memory and can be operated on/with in the same ways).
    pub fn is_compatible_with(&self, other: &RichType) -> bool {
        match (self, other) {
            (RichType::Bool, RichType::Bool)
            | (RichType::I64, RichType::I64)
            | (RichType::String, RichType::String) => true,
            (RichType::Struct(s1), RichType::Struct(s2)) => {
                // Struct types are compatible if, for every n, the nth fields on both structs have
                // the same names and compatible types.
                if s1.fields.len() != s2.fields.len() {
                    return false;
                }

                for (field1, field2) in s1.fields.iter().zip(s2.fields.iter()) {
                    if field1.name != field2.name || !field1.typ.is_compatible_with(&field2.typ) {
                        return false;
                    }
                }

                true
            }
            (RichType::Function(f1), RichType::Function(f2)) => {
                // Function types are equal if they have compatible return types and, for each n,
                // arguments n in both functions have compatible types.
                if f1.args.len() != f2.args.len() {
                    return false;
                }

                for (arg1, arg2) in f1.args.iter().zip(f2.args.iter()) {
                    if !arg1.typ.is_compatible_with(&arg2.typ) {
                        return false;
                    }
                }

                true
            }
            (_, _) => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::analyzer::func::{RichArg, RichFnSig};
    use crate::analyzer::r#struct::{RichField, RichStruct};
    use crate::analyzer::r#type::RichType;

    #[test]
    fn partial_eq() {
        assert_eq!(RichType::Bool, RichType::Bool);
        assert_eq!(RichType::String, RichType::String);
        assert_eq!(RichType::I64, RichType::I64);
        assert_eq!(
            RichType::Struct(RichStruct {
                name: "asdf".to_string(),
                fields: vec![RichField {
                    name: "field".to_string(),
                    typ: RichType::Bool,
                }],
            }),
            RichType::Struct(RichStruct {
                name: "asdf".to_string(),
                fields: vec![RichField {
                    name: "field".to_string(),
                    typ: RichType::Bool,
                }],
            })
        );
        assert_eq!(
            RichType::Function(Box::new(RichFnSig {
                name: "test_func".to_string(),
                args: vec![RichArg {
                    name: "arg1".to_string(),
                    typ: RichType::Bool,
                }],
                return_type: Some(RichType::String),
            })),
            RichType::Function(Box::new(RichFnSig {
                name: "test_func".to_string(),
                args: vec![RichArg {
                    name: "arg1".to_string(),
                    typ: RichType::Bool,
                }],
                return_type: Some(RichType::String),
            }))
        )
    }
}
