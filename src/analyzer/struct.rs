use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::{Debug, Display, Formatter};

use colored::Colorize;

use crate::analyzer::error::AnalyzeResult;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::{check_type_containment, RichType, TypeId};
use crate::fmt::hierarchy_to_string;
use crate::parser::r#struct::{StructInit, StructType};
use crate::{format_code, util};

/// Represents a semantically valid and type-rich struct field.
#[derive(Clone, Debug, PartialEq)]
pub struct RichField {
    pub name: String,
    pub type_id: TypeId,
}

impl Display for RichField {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.type_id)
    }
}

/// Represents a semantically valid and type-rich structure.
#[derive(Clone, Debug)]
pub struct RichStructType {
    pub name: String,
    pub fields: Vec<RichField>,
}

impl Display for RichStructType {
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

impl PartialEq for RichStructType {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && util::vecs_eq(&self.fields, &other.fields)
    }
}

impl RichStructType {
    /// Performs semantic analysis on a struct type declaration. Note that this will also
    /// recursively analyze any types contained in the struct. On success, the struct type info will
    /// be stored in the program context.
    /// If `anon` is true, the struct type is expected to be declared inline without a type
    /// name.
    pub fn from(ctx: &mut ProgramContext, struct_type: &StructType, anon: bool) -> Self {
        if !anon {
            if struct_type.name.is_empty() {
                ctx.add_err(AnalyzeError::new(
                    ErrorKind::MissingTypeName,
                    "struct types declared in this context must have names",
                    struct_type,
                ));
            }

            // Check if the struct type is already defined in the program context. This will be the
            // case if we've already analyzed it in the process of analyzing another type that
            // contains this type.
            if let Some(rich_struct) = ctx.get_struct(struct_type.name.as_str()) {
                return rich_struct.clone();
            }
        } else if anon && !struct_type.name.is_empty() {
            ctx.add_err(
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
        let type_id = TypeId::new_unresolved(struct_type.name.as_str());
        ctx.add_resolved_type(
            type_id.clone(),
            RichType::Struct(RichStructType {
                name: struct_type.name.clone(),
                fields: vec![],
            }),
        );

        // Analyze the struct fields.
        let mut fields = vec![];
        let mut field_names = HashSet::new();
        for field in &struct_type.fields {
            // Check for duplicated field name.
            if !field_names.insert(field.name.clone()) {
                ctx.add_err(AnalyzeError::new(
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

            // Resolve the struct field type and add it to the list of analyzed fields.
            fields.push(RichField {
                name: field.name.clone(),
                type_id: RichType::analyze(ctx, &field.typ),
            });
        }

        let rich_struct = RichStructType {
            name: struct_type.name.clone(),
            fields,
        };

        // Make sure the struct doesn't contain itself via other types.
        let rich_struct_type = RichType::Struct(rich_struct.clone());
        if let Some(type_hierarchy) = rich_struct_type.contains_type(ctx, &rich_struct_type) {
            ctx.add_err(
                AnalyzeError::new(
                    ErrorKind::InfiniteSizedType,
                    format_code!(
                        "struct {} cannot contain itself via any of its field types",
                        rich_struct.name,
                    )
                    .as_str(),
                    struct_type,
                )
                .with_detail(
                    format!(
                        "The offending type hierarchy is {}.",
                        hierarchy_to_string(type_hierarchy.iter().map(|t| t.to_string()).collect())
                    )
                    .as_str(),
                )
                .with_help("Consider using reference types instead."),
            );
        }

        ctx.add_struct(rich_struct.clone());
        ctx.add_resolved_type(type_id, RichType::Struct(rich_struct.clone()));
        rich_struct
    }

    /// Returns the type of the struct field with the given name.
    pub fn get_field_type(&self, name: &str) -> Option<&TypeId> {
        for field in &self.fields {
            if field.name.as_str() == name {
                return Some(&field.type_id);
            }
        }

        None
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
pub struct RichStructInit {
    pub type_id: TypeId,
    /// Maps struct field names to their values.
    pub field_values: HashMap<String, RichExpr>,
}

impl Display for RichStructInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {{ ... }}", self.type_id)
    }
}

impl PartialEq for RichStructInit {
    fn eq(&self, other: &Self) -> bool {
        self.type_id == other.type_id
    }
}

impl RichStructInit {
    /// Performs semantic analysis on struct initialization.
    pub fn from(ctx: &mut ProgramContext, struct_init: &StructInit) -> Self {
        // Resolve the struct type.
        let type_id = RichType::analyze(ctx, &struct_init.typ);
        let rich_type = ctx.must_get_resolved_type(&type_id).clone();
        let struct_type = match rich_type {
            RichType::Struct(s) => s,
            RichType::Unknown(type_name) => {
                // The struct type has already failed semantic analysis, so we should avoid
                // analyzing its initialization and just return some zero-value placeholder instead.
                return RichStructInit {
                    type_id: TypeId::new_unresolved(type_name.as_str()),
                    field_values: Default::default(),
                };
            }
            other => {
                panic!("found invalid struct type {}", other);
            }
        };

        // Analyze struct field assignments and collect errors.
        let mut errors = vec![];
        let mut field_values: HashMap<String, RichExpr> = HashMap::new();
        for (field_name, field_value) in &struct_init.field_values {
            // Get the struct field type, or error if the struct type has no such field.
            let field_type = match struct_type.get_field_type(field_name.as_str()) {
                Some(typ) => typ,
                None => {
                    errors.push(AnalyzeError::new(
                        ErrorKind::StructFieldNotDefined,
                        format_code!("struct type {} has no field {}", struct_type, field_name)
                            .as_str(),
                        // TODO: This should be the location of the bad field instead of the entire
                        // struct init.
                        struct_init,
                    ));

                    // Skip this struct field since it's invalid.
                    continue;
                }
            };

            // Analyze the value being assigned to the struct field.
            let expr = RichExpr::from(ctx, field_value.clone(), Some(field_type));

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
                        struct_type,
                    )
                    .as_str(),
                    struct_init,
                ));
            }
        }

        // Move all analysis errors into the program context. We're not adding them immediately
        // to avoid borrow issues.
        for err in errors {
            ctx.add_err(err);
        }

        RichStructInit {
            type_id,
            field_values,
        }
    }
}

/// Analyzes type containment within the given struct type and returns an error if there are any
/// illegal type containment cycles that would result in infinite-sized types.
pub fn check_struct_containment_cycles(
    ctx: &ProgramContext,
    struct_type: &StructType,
    hierarchy: &mut Vec<String>,
) -> AnalyzeResult<()> {
    if hierarchy.contains(&struct_type.name) {
        return Err(AnalyzeError::new(
            ErrorKind::InfiniteSizedType,
            format_code!("struct type {} cannot contain itself", struct_type.name).as_str(),
            struct_type,
        ));
    }

    // Push this type name onto the hierarchy stack so it can be checked against other types.
    hierarchy.push(struct_type.name.clone());

    // Recursively check each struct field type.
    for field in &struct_type.fields {
        check_type_containment(ctx, &field.typ, hierarchy)?;
    }

    // Pop this type name off the hierarchy stack because all types it contains have been
    // checked.
    hierarchy.pop();

    Ok(())
}
