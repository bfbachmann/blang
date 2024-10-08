use std::collections::HashSet;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::params::AParams;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::fmt::format_code_vec;
use crate::parser::ast::r#struct::{StructInit, StructType};
use crate::parser::ast::r#type::Type;
use crate::{format_code, util};

/// Represents a semantically valid and type-rich struct field.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AField {
    pub name: String,
    pub type_key: TypeKey,
}

impl Display for AField {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.type_key)
    }
}

/// Represents a semantically valid and type-rich structure.
#[derive(Clone, Debug)]
pub struct AStructType {
    pub name: String,
    pub mangled_name: String,
    pub maybe_params: Option<AParams>,
    pub fields: Vec<AField>,
}

impl Display for AStructType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let params = match &self.maybe_params {
            Some(params) => format!("{params}"),
            None => "".to_string(),
        };
        write!(f, "{}{}", self.name, params)
    }
}

impl PartialEq for AStructType {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.mangled_name == other.mangled_name
            && self.maybe_params == other.maybe_params
            && util::vecs_eq(&self.fields, &other.fields)
    }
}

impl AStructType {
    /// Performs semantic analysis on a struct type declaration. Note that this will also
    /// recursively analyze any types contained in the struct. On success, the struct type info will
    /// be stored in the program context.
    /// If `anon` is true, the struct type is expected to be declared inline without a type
    /// name.
    pub fn from(ctx: &mut ProgramContext, struct_type: &StructType, anon: bool) -> Self {
        if !anon {
            if struct_type.name.is_empty() {
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::MissingTypeName,
                    "struct types declared in this context must have names",
                    struct_type,
                ));
            }

            // Check if the struct type is already defined in the program context. This will be the
            // case if we've already analyzed it in the process of analyzing another type that
            // contains this type.
            if let Some(a_struct) = ctx.get_struct_type(None, struct_type.name.as_str()) {
                return a_struct.clone();
            }
        } else if !struct_type.name.is_empty() {
            ctx.insert_err(
                AnalyzeError::new(
                    ErrorKind::UnexpectedTypeName,
                    "inline struct type definitions cannot have type names",
                    struct_type,
                )
                .with_help(
                    format_code!("Consider removing the type name {}.", struct_type.name).as_str(),
                ),
            );
        }

        // Before analyzing struct field types, we'll prematurely add this (currently-empty) struct
        // type to the program context. This way, if any of the field types make use of this struct
        // type, we won't get into an infinitely recursive type resolution cycle. When we're done
        // analyzing this struct type, the mapping will be updated in the program context.
        let mangled_name = ctx.mangle_name(None, None, struct_type.name.as_str(), true);
        let mut a_struct_type = AStructType {
            name: struct_type.name.clone(),
            mangled_name: mangled_name.clone(),
            maybe_params: None,
            fields: vec![],
        };
        let type_key = ctx.insert_type(AType::Struct(a_struct_type.clone()));

        // Analyze generic params, if any and push them to the program context.
        let maybe_params = match &struct_type.maybe_params {
            Some(params) => {
                let params = AParams::from(ctx, params, type_key);
                ctx.push_params(params.clone());
                Some(params)
            }
            None => None,
        };

        // Update the stored type with the resolved parameters. It's important that we do this
        // before analyzing any fields because the field types may reference this type, in
        // which case it's important that we know what parameters it expects.
        a_struct_type.maybe_params = maybe_params.clone();
        ctx.replace_type(type_key, AType::Struct(a_struct_type));

        // Analyze the struct fields.
        let mut fields = vec![];
        let mut field_names = HashSet::new();
        for field in &struct_type.fields {
            // Check for duplicated field name.
            if !field_names.insert(field.name.clone()) {
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::DuplicateStructField,
                    format_code!(
                        "struct type {} already has a field named {}",
                        struct_type.name,
                        field.name,
                    )
                    .as_str(),
                    field,
                ));

                // Skip the duplicated field.
                continue;
            }

            // Mark the struct field as public if necessary.
            if field.is_pub {
                ctx.mark_struct_field_pub(type_key, field.name.as_str());
            }

            // Resolve the struct field type and add it to the list of analyzed fields.
            fields.push(AField {
                name: field.name.clone(),
                type_key: ctx.resolve_type(&field.typ),
            });
        }

        // Update the type in the type store now that we've analyzed its fields.
        let has_params = maybe_params.is_some();
        let a_struct_type = AStructType {
            name: struct_type.name.clone(),
            mangled_name,
            maybe_params,
            fields,
        };
        ctx.replace_type(type_key, AType::Struct(a_struct_type.clone()));

        if has_params {
            // We've analyzed all the fields on this struct, but it's possible that some of the
            // fields had types that were monomorphizations of this struct type. For example, in
            // this struct
            //
            //      struct Thing[T] { ptr: *Thing[int] }
            //
            // the `ptr` field type `*Thing[int]` references a monomorphization of the `Thing` type.
            // If this happens, the monomorphization would actually not be correct at this point
            // because it happened before any of the fields on this type had been analyzed and
            // written back to the type store. In other words, the monomorphization would have
            // happened on an empty type, so we need to redo it on the analyzed type.
            if let Some(monos) = ctx.monomorphized_types.remove(&type_key) {
                for mono in monos {
                    ctx.reexecute_monomorphization(mono);
                }
            }

            // Pop generic parameters now that we're done analyzing the type.
            ctx.pop_params();
        }

        // Record the type name as public in the current module if necessary.
        if struct_type.is_pub {
            ctx.insert_pub_type_name(struct_type.name.as_str());
        }

        a_struct_type
    }

    /// Returns the type of the struct field with the given name.
    pub fn get_field_type_key(&self, name: &str) -> Option<TypeKey> {
        match self.fields.iter().find(|f| f.name.as_str() == name) {
            Some(field) => Some(field.type_key),
            None => None,
        }
    }

    /// Returns the index of the field with the given name.
    pub fn get_field_index(&self, name: &str) -> Option<usize> {
        for (i, field) in self.fields.iter().enumerate() {
            if field.name.as_str() == name {
                return Some(i);
            }
        }

        None
    }
}

/// Represents a semantically valid struct initialization.
#[derive(Debug, Clone)]
pub struct AStructInit {
    pub type_key: TypeKey,
    pub field_values: Vec<(String, AExpr)>,
}

impl Display for AStructInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {{ ... }}", self.type_key)
    }
}

impl PartialEq for AStructInit {
    fn eq(&self, other: &Self) -> bool {
        self.type_key == other.type_key
    }
}

impl AStructInit {
    /// Performs semantic analysis on struct initialization.
    pub fn from(ctx: &mut ProgramContext, struct_init: &StructInit) -> Self {
        // Resolve the struct type.
        let type_key = ctx.resolve_type(&Type::Unresolved(struct_init.typ.clone()));
        let struct_type = match ctx.must_get_type(type_key) {
            AType::Unknown(_) => {
                // The struct type has already failed semantic analysis, so we should avoid
                // analyzing its initialization and just return some zero-value placeholder instead.
                return AStructInit {
                    type_key,
                    field_values: Default::default(),
                };
            }

            AType::Struct(s) => s.clone(),

            _ => {
                // This is not a struct type. Record the error and return a placeholder value.
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::TypeIsNotStruct,
                    format_code!(
                        "type {} is not a struct, but is being used like one",
                        ctx.display_type(type_key)
                    )
                    .as_str(),
                    struct_init,
                ));

                return AStructInit {
                    type_key,
                    field_values: Default::default(),
                };
            }
        };

        // Analyze struct field assignments and collect errors.
        let mut errors = vec![];
        let mut field_values: Vec<(String, AExpr)> = vec![];
        let mut used_field_names = HashSet::new();
        for (field_name_symbol, field_value) in &struct_init.field_values {
            let field_name = field_name_symbol.name.as_str();

            // Get the struct field type, or error if the struct type has no such field.
            let field_tk = match struct_type.get_field_type_key(field_name) {
                Some(tk) => tk,
                None => {
                    errors.push(AnalyzeError::new(
                        ErrorKind::UndefStructField,
                        format_code!(
                            "struct type {} has no field {}",
                            ctx.display_type(type_key),
                            field_name
                        )
                        .as_str(),
                        field_name_symbol,
                    ));

                    // Skip this struct field since it's invalid.
                    continue;
                }
            };

            // Record an error if the struct field is not settable from the current
            // module.
            if !ctx.struct_field_is_accessible(type_key, field_name) {
                errors.push(AnalyzeError::new(
                    ErrorKind::UseOfPrivateValue,
                    format_code!("{} is not public", field_name).as_str(),
                    field_name_symbol,
                ));
            }

            // Analyze the value being assigned to the struct field.
            let expr = AExpr::from(ctx, field_value.clone(), Some(field_tk), false, false);

            // Insert the analyzed struct field value, making sure that it was not already assigned.
            if used_field_names.insert(field_name.to_string()) {
                field_values.push((field_name.to_string(), expr));
            } else {
                errors.push(AnalyzeError::new(
                    ErrorKind::DuplicateStructField,
                    format_code!("struct field {} is already assigned", field_name).as_str(),
                    field_name_symbol,
                ));
            }
        }

        // Make sure all struct fields were assigned.
        let mut uninit_field_names = vec![];
        for field in &struct_type.fields {
            if field_values
                .iter()
                .find(|(name, _)| name == &field.name)
                .is_none()
            {
                uninit_field_names.push(field.name.as_str());
            }
        }

        if !uninit_field_names.is_empty() {
            errors.push(AnalyzeError::new(
                ErrorKind::StructFieldNotInitialized,
                format!(
                    "{} {} on struct type {} {} uninitialized",
                    match uninit_field_names.len() {
                        1 => "field",
                        _ => "fields",
                    },
                    format_code_vec(&uninit_field_names, ", "),
                    format_code!(ctx.display_type(type_key)),
                    match uninit_field_names.len() {
                        1 => "is",
                        _ => "are",
                    },
                )
                .as_str(),
                &struct_init.typ,
            ));
        }

        // Move all analysis errors into the program context. We're not adding them immediately
        // to avoid borrow issues.
        for err in errors {
            ctx.insert_err(err);
        }

        AStructInit {
            type_key,
            field_values,
        }
    }

    /// Returns the human-readable version of this struct initialization.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        format!("{} {{ ... }}", ctx.display_type(self.type_key))
    }

    /// Returns the value assigned to the field with the given name. Panics if
    /// no such field exists.
    pub fn must_get_field_value(&self, name: &str) -> &AExpr {
        let (_, value) = self
            .field_values
            .iter()
            .find(|(field_name, _)| field_name == name)
            .unwrap();
        value
    }
}
