use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::{Debug, Display, Formatter};

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
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

impl AField {
    /// Returns a string containing the human-readable version of this struct field.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        format!("{}: {}", self.name, ctx.display_type_for_key(self.type_key))
    }
}

/// Represents a semantically valid and type-rich structure.
#[derive(Clone, Debug)]
pub struct AStructType {
    pub name: String,
    pub fields: Vec<AField>,
}

impl Display for AStructType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.name == "" {
            write!(f, "struct {{")?;

            for field in &self.fields {
                write!(f, "{}", field)?;
            }

            write!(f, "}}")
        } else {
            write!(f, "{}", self.name)
        }
    }
}

impl PartialEq for AStructType {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && util::vecs_eq(&self.fields, &other.fields)
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
            // todo
            if let Some(a_struct) = ctx.get_struct_type(None, struct_type.name.as_str()) {
                return a_struct.clone();
            }
        } else if anon && !struct_type.name.is_empty() {
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
        let type_key = ctx.insert_type(AType::Struct(AStructType {
            name: struct_type.name.clone(),
            fields: vec![],
        }));

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

        // Now sort struct fields by size. The fields should already be sorted alphabetically, so
        // ties in their size are broken by lexicographical order. This is done to save memory by
        // reducing the need for padding between struct fields in memory.
        fields.sort_by(|f1, f2| {
            let type1 = ctx.must_get_type(f1.type_key);
            let type2 = ctx.must_get_type(f2.type_key);
            type2
                .min_size_bytes(&ctx.type_store)
                .cmp(&type1.min_size_bytes(&ctx.type_store))
        });

        let a_struct = AStructType {
            name: struct_type.name.clone(),
            fields,
        };

        // Record the type name as public in the current module if necessary.
        if struct_type.is_pub {
            ctx.insert_pub_type_name(struct_type.name.as_str());
        }

        let a_struct_type = AType::Struct(a_struct.clone());
        ctx.replace_type(type_key, a_struct_type);
        a_struct
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

    /// Returns a string containing the human-readable representation of the struct type.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        if self.name == "" {
            let mut s = format!("struct {{");

            for field in &self.fields {
                s += format!("{}", field.display(ctx)).as_str();
            }

            s + format!("}}").as_str()
        } else {
            format!("{}", self.name)
        }
    }
}

/// Represents a semantically valid struct initialization.
#[derive(Debug, Clone)]
pub struct AStructInit {
    pub type_key: TypeKey,
    /// Maps struct field names to their values.
    pub field_values: HashMap<String, AExpr>,
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
        let type_key = ctx.resolve_type(&struct_init.typ);
        let struct_type = match ctx.must_get_type(type_key) {
            AType::Struct(s) => s.clone(),
            AType::Unknown(type_name) => {
                // The struct type has already failed semantic analysis, so we should avoid
                // analyzing its initialization and just return some zero-value placeholder instead.
                return AStructInit {
                    type_key: ctx.resolve_type(&Type::new_unresolved(type_name.as_str())),
                    field_values: Default::default(),
                };
            }
            other => {
                panic!("found invalid struct type {}", other);
            }
        };

        // Analyze struct field assignments and collect errors.
        let mut errors = vec![];
        let mut field_values: HashMap<String, AExpr> = HashMap::new();
        for (field_name, field_value) in &struct_init.field_values {
            // Get the struct field type, or error if the struct type has no such field.
            let field_type = match struct_type.get_field_type_key(field_name.as_str()) {
                Some(typ) => typ,
                None => {
                    errors.push(AnalyzeError::new(
                        ErrorKind::UndefStructField,
                        format_code!(
                            "struct type {} has no field {}",
                            struct_type.display(ctx),
                            field_name
                        )
                        .as_str(),
                        // TODO: This should be the location of the bad field.
                        field_value,
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
                    field_value,
                ));
            }

            // Analyze the value being assigned to the struct field.
            let expr = AExpr::from(
                ctx,
                field_value.clone(),
                Some(field_type),
                false,
                false,
                false,
            );

            // Insert the analyzed struct field value, making sure that it was not already assigned.
            if field_values.insert(field_name.to_string(), expr).is_some() {
                errors.push(AnalyzeError::new(
                    ErrorKind::DuplicateStructField,
                    format_code!("struct field {} is already assigned", &field_name).as_str(),
                    field_value,
                ));
            }
        }

        // Make sure all struct fields were assigned.
        for field in &struct_type.fields {
            if !field_values.contains_key(field.name.as_str()) {
                errors.push(AnalyzeError::new(
                    ErrorKind::StructFieldNotInitialized,
                    format_code!(
                        "field {} on struct type {} is uninitialized",
                        field.name,
                        struct_type.display(ctx),
                    )
                    .as_str(),
                    struct_init,
                ));
            }
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
        format!("{} {{ ... }}", ctx.display_type_for_key(self.type_key))
    }
}
