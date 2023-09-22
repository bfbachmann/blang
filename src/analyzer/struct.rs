use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::{Debug, Display, Formatter};

use colored::Colorize;

use crate::analyzer::error::AnalyzeResult;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::fmt::hierarchy_to_string;

use crate::parser::r#struct::{StructInit, StructType};
use crate::parser::r#type::Type;

use crate::{format_code, util};

/// Represents a semantically valid and type-rich struct field.
#[derive(Clone, Debug, PartialEq)]
pub struct RichField {
    pub name: String,
    pub type_id: TypeId,
}

impl Display for RichField {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.type_id, self.name)
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
        self.name == other.name && util::vectors_are_equal(&self.fields, &other.fields)
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
                ctx.add_err(AnalyzeError::new_with_locatable(
                    ErrorKind::MissingTypeName,
                    "struct types declared in this context must have names",
                    Box::new(struct_type.clone()),
                ));
            }

            // Check if the struct type is already defined in the program context. This will be the case
            // if we've already analyzed it in the process of analyzing another type that contains
            // this type.
            if let Some(rich_struct) = ctx.get_struct(struct_type.name.as_str()) {
                return rich_struct.clone();
            }
        } else if anon && !struct_type.name.is_empty() {
            ctx.add_err(
                AnalyzeError::new_with_locatable(
                    ErrorKind::UnexpectedTypeName,
                    "inline struct type definitions cannot have type names",
                    Box::new(struct_type.clone()),
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
        let type_id = TypeId::from(Type::new_unknown(struct_type.name.as_str()));
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
                ctx.add_err(AnalyzeError::new_with_locatable(
                    ErrorKind::DuplicateStructFieldName,
                    format_code!(
                        "struct type {} cannot have multiple fields named {}",
                        struct_type.name,
                        field.name,
                    )
                    .as_str(),
                    Box::new(field.clone()),
                ));

                // Skip the duplicated field.
                continue;
            }

            // Make sure the struct field type is not the same as this struct type to prevent
            // containment cycles causing types of infinite size.
            if let Type::Unresolved(unresolved_type) = &field.typ {
                if unresolved_type.name == struct_type.name {
                    ctx.add_err(
                        AnalyzeError::new_with_locatable(
                            ErrorKind::InfiniteSizedType,
                            format_code!(
                                "struct {} cannot directly contain itself (via field {})",
                                struct_type.name,
                                field.name,
                            )
                            .as_str(),
                            Box::new(field.clone()),
                        )
                        .with_help(
                            format_code!(
                                "Consider changing field {} to {}",
                                format!("{}: {}", field.name, unresolved_type.name),
                                format!("{}: &{}", field.name, unresolved_type.name),
                            )
                            .as_str(),
                        ),
                    );

                    // Skip the invalid field.
                    continue;
                }
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
                AnalyzeError::new_with_locatable(
                    ErrorKind::InfiniteSizedType,
                    format_code!(
                        "struct {} cannot contain itself via any of its field types",
                        rich_struct.name,
                    )
                    .as_str(),
                    Box::new(struct_type.clone()),
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

    /// Recursively checks for struct containment cycles that would imply struct types with infinite
    /// size.
    pub fn analyze_containment(
        ctx: &ProgramContext,
        struct_type: &StructType,
    ) -> AnalyzeResult<()> {
        RichStructType::check_containment_cycles(ctx, struct_type, &mut vec![])
    }

    fn check_containment_cycles(
        ctx: &ProgramContext,
        struct_type: &StructType,
        hierarchy: &mut Vec<String>,
    ) -> AnalyzeResult<()> {
        hierarchy.push(struct_type.name.clone());

        for field in &struct_type.fields {
            match &field.typ {
                Type::Unresolved(unresolved_type) => {
                    if hierarchy.contains(&unresolved_type.name) {
                        hierarchy.push(unresolved_type.name.to_string());
                        return Err(AnalyzeError::new_with_locatable(
                            ErrorKind::InfiniteSizedType,
                            format_code!(
                                "type {} cannot contain itself (via field {} on struct type {})",
                                unresolved_type.name,
                                field.name,
                                struct_type,
                            )
                            .as_str(),
                            Box::new(field.clone()),
                        )
                        .with_detail(
                            format!(
                                "The offending type hierarchy is {}.",
                                hierarchy_to_string(hierarchy.clone())
                            )
                            .as_str(),
                        )
                        .with_help(
                            format_code!(
                                "Consider changing field {} to {}",
                                format!("{}: {}", field.name, unresolved_type.name),
                                format!("{}: &{}", field.name, unresolved_type.name),
                            )
                            .as_str(),
                        ));
                    }

                    match ctx.get_extern_struct(unresolved_type.name.as_str()) {
                        Some(field_struct_type) => {
                            RichStructType::check_containment_cycles(
                                ctx,
                                field_struct_type,
                                hierarchy,
                            )?;
                            hierarchy.pop();
                        }
                        None => {
                            // This type is not defined.
                        }
                    };
                }

                Type::Struct(field_struct_type) => {
                    if !field_struct_type.name.is_empty()
                        && hierarchy.contains(&field_struct_type.name)
                    {
                        return Err(AnalyzeError::new_with_locatable(
                            ErrorKind::InfiniteSizedType,
                            format_code!(
                                "type {} cannot contain itself (via struct field {} on struct \
                                type {})",
                                field_struct_type.name,
                                field.name,
                                struct_type.name,
                            )
                            .as_str(),
                            Box::new(field.clone()),
                        )
                        .with_help(
                            format_code!(
                                "Consider changing field {} to {}.",
                                format!("{}: {}", field.name, field_struct_type),
                                format!("{}: &{}", field.name, field_struct_type),
                            )
                            .as_str(),
                        ));
                    }

                    hierarchy.push(field_struct_type.name.clone());
                    RichStructType::check_containment_cycles(ctx, field_struct_type, hierarchy)?;
                    hierarchy.pop();
                }

                Type::I64(_) | Type::String(_) | Type::Bool(_) | Type::Function(_) => {}
            }
        }

        Ok(())
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
    pub typ: RichStructType,
    /// Maps struct field names to their values.
    pub field_values: HashMap<String, RichExpr>,
}

impl Display for RichStructInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {{ ... }}", self.typ)
    }
}

impl PartialEq for RichStructInit {
    fn eq(&self, other: &Self) -> bool {
        self.typ == other.typ
    }
}

impl RichStructInit {
    /// Performs semantic analysis on struct initialization.
    pub fn from(ctx: &mut ProgramContext, struct_init: &StructInit) -> Self {
        // Resolve the struct type.
        let type_id = RichType::analyze(ctx, &struct_init.typ);
        let rich_type = ctx.get_resolved_type(&type_id).unwrap().clone();
        let struct_type = match rich_type {
            RichType::Struct(s) => s,
            RichType::Unknown(type_name) => {
                // The struct type has already failed semantic analysis, so we should avoid
                // analyzing its initialization and just return some zero-value placeholder instead.
                return RichStructInit {
                    typ: RichStructType {
                        name: type_name.clone(),
                        fields: vec![],
                    },
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
                    errors.push(AnalyzeError::new_with_locatable(
                        ErrorKind::StructFieldNotDefined,
                        format_code!("struct type {} has no field {}", struct_type, field_name,)
                            .as_str(),
                        // TODO: This should be the location of the bad field instead of the entire
                        // struct init.
                        Box::new(struct_init.clone()),
                    ));

                    // Skip this struct field since it's invalid.
                    continue;
                }
            };

            // Analyze the value being assigned to the struct field.
            let expr = RichExpr::from(ctx, field_value.clone());

            // Make sure the value being assigned to the field has the expected type.
            if &expr.type_id != field_type {
                errors.push(AnalyzeError::new_with_locatable(
                    ErrorKind::IncompatibleTypes,
                    format_code!(
                        "cannot assign expression of type {} to field {} on struct type {}",
                        format!("{}", &expr.type_id),
                        format!("{}: {}", &field_name, &field_type),
                        format!("{}", &struct_type),
                    )
                    .as_str(),
                    Box::new(field_value.clone()),
                ));
            }

            // Insert the analyzed struct field value, making sure that it was not already assigned.
            if field_values.insert(field_name.to_string(), expr).is_some() {
                errors.push(AnalyzeError::new_with_locatable(
                    ErrorKind::DuplicateStructFieldName,
                    format_code!("struct field {} is already assigned", &field_name).as_str(),
                    Box::new(field_value.clone()),
                ));
            }
        }

        // Make sure all struct fields were assigned.
        for field in &struct_type.fields {
            if !field_values.contains_key(field.name.as_str()) {
                errors.push(AnalyzeError::new_with_locatable(
                    ErrorKind::StructFieldNotInitialized,
                    format_code!(
                        "field {} on struct type {} is uninitialized",
                        field.name,
                        struct_type,
                    )
                    .as_str(),
                    Box::new(struct_init.clone()),
                ));
            }
        }

        let typ = struct_type.clone();

        // Move all analysis errors into the program context. We're not adding them immediately
        // to avoid borrow issues.
        for err in errors {
            ctx.add_err(err);
        }

        RichStructInit { typ, field_values }
    }
}
