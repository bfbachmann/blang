use core::fmt;
use std::fmt::Formatter;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#struct::RichStruct;
use crate::analyzer::AnalyzeResult;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::r#type::Type;

/// Represents a semantically valid and fully resolved type.
#[derive(Clone, PartialEq, Debug)]
pub enum RichType {
    Bool,
    String,
    I64,
    Struct(RichStruct),
    Function(FunctionSignature),
}

impl fmt::Display for RichType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            RichType::Bool => write!(f, "bool"),
            RichType::String => write!(f, "string"),
            RichType::I64 => write!(f, "i64"),
            RichType::Struct(s) => write!(f, "{}", s),
            RichType::Function(func) => write!(f, "{}", func),
        }
    }
}

impl RichType {
    /// Analyzes and resolves the given type (if unresolved) and returns it. This will also store
    /// type information in the program context.
    pub fn from(ctx: &mut ProgramContext, typ: &Type) -> AnalyzeResult<Self> {
        return match typ {
            Type::Unresolved(type_name) => {
                // If the type has already been analyzed, just return it.
                if let Some(rich_struct_type) = ctx.get_struct(type_name) {
                    return Ok(RichType::Struct(rich_struct_type.clone()));
                }
                if let Some(fn_sig) = ctx.get_extern_fn(type_name) {
                    return Ok(RichType::Function(fn_sig.clone()));
                }
                if let Some(fn_type) = ctx.get_fn(type_name) {
                    return Ok(RichType::Function(fn_type.signature.clone()));
                }

                // The type has not yet been analyzed, so make sure the type has at least been
                // declared somewhere and analyze it.
                if let Some(struct_type) = ctx.get_extern_struct(type_name) {
                    let rich_struct_type = RichStruct::from(ctx, &struct_type.clone())?;
                    return Ok(RichType::Struct(rich_struct_type));
                }

                return Err(AnalyzeError::new(
                    ErrorKind::TypeNotDefined,
                    format!("type {} is not defined", type_name).as_str(),
                ));
            }

            Type::I64 => Ok(RichType::I64),

            Type::Bool => Ok(RichType::Bool),

            Type::String => Ok(RichType::String),

            Type::Function(sig) => Ok(RichType::Function(*sig.clone())),

            Type::Struct(struct_type) => {
                let rich_struct_type = RichStruct::from(ctx, struct_type)?;
                return Ok(RichType::Struct(rich_struct_type));
            }
        };
    }

    /// Returns true if this type contains the given type. For this to be the case, this type must
    /// be a container (struct, vector, array, etc).
    pub fn contains_type(&self, typ: &RichType) -> bool {
        return match self {
            RichType::Bool | RichType::I64 | RichType::String | RichType::Function(_) => false,
            RichType::Struct(s) => {
                for field in &s.fields {
                    if &field.typ == typ || field.typ.contains_type(typ) {
                        return true;
                    }
                }

                false
            }
        };
    }
}
