use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::{Debug, Display, Formatter};

use colored::Colorize;

use crate::analyzer::error::AnalyzeResult;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::RichType;
use crate::parser::r#struct::{StructInit, StructType};
use crate::parser::r#type::Type;
use crate::util;

/// Represents a semantically valid and type-rich struct field.
#[derive(Clone, Debug, PartialEq)]
pub struct RichField {
    pub name: String,
    pub typ: RichType,
}

impl Display for RichField {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.typ, self.name)
    }
}

/// Represents a semantically valid and type-rich structure.
#[derive(Clone, Debug)]
pub struct RichStruct {
    pub name: String,
    pub fields: Vec<RichField>,
}

impl Display for RichStruct {
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

impl PartialEq for RichStruct {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && util::vectors_are_equal(&self.fields, &other.fields)
    }
}

impl RichStruct {
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
            ctx.add_err(AnalyzeError::new_with_locatable(
                ErrorKind::UnexpectedTypeName,
                format!(
                    "inline struct type definitions cannot have type names (remove type name `{}`)",
                    struct_type.name.blue()
                )
                .as_str(),
                Box::new(struct_type.clone()),
            ));
        }

        // Analyze the struct fields.
        let mut fields = vec![];
        let mut field_names = HashSet::new();
        for field in &struct_type.fields {
            // Check for duplicated field name.
            if !field_names.insert(field.name.clone()) {
                ctx.add_err(AnalyzeError::new_with_locatable(
                    ErrorKind::DuplicateStructFieldName,
                    format!(
                        "struct type `{}` cannot have multiple fields named `{}`",
                        struct_type.name.blue(),
                        field.name.blue(),
                    )
                    .as_str(),
                    Box::new(field.clone()),
                ));
                continue;
            }

            // Make sure the struct field type is not the same as this struct type to prevent
            // containment cycles causing types of infinite size.
            if let Type::Unresolved(unresolved_type) = &field.typ {
                if unresolved_type.name == struct_type.name {
                    ctx.add_err(
                        AnalyzeError::new_with_locatable(
                            ErrorKind::InfiniteSizedType,
                            format!(
                                "struct `{}` cannot directly contain itself (via field `{}`)",
                                struct_type.name.blue(),
                                field.name.blue(),
                            )
                            .as_str(),
                            Box::new(field.clone()),
                        )
                        .with_hint(
                            format!(
                                "consider changing field `{}: {}` to `{}: &{}`",
                                field.name.blue(),
                                unresolved_type.name.blue(),
                                field.name.blue(),
                                unresolved_type.name.blue(),
                            )
                            .as_str(),
                        ),
                    );
                    continue;
                }
            }

            // Resolve the struct field type and add it to the list of analyzed fields.
            fields.push(RichField {
                name: field.name.clone(),
                typ: RichType::from(ctx, &field.typ),
            });
        }

        let rich_struct = RichStruct {
            name: struct_type.name.clone(),
            fields,
        };

        // Make sure the struct doesn't contain itself via other types.
        let rich_struct_type = RichType::Struct(rich_struct.clone());
        if let Some(type_hierarchy) = rich_struct_type.contains_type(&rich_struct_type) {
            ctx.add_err(
                AnalyzeError::new_with_locatable(
                    ErrorKind::InfiniteSizedType,
                    format!(
                        "struct `{}` cannot contain itself via any of its field types",
                        rich_struct.name.blue()
                    )
                    .as_str(),
                    Box::new(struct_type.clone()),
                )
                .with_detail(
                    format!(
                        "the offending type hierarchy is {}",
                        RichType::hierarchy_to_string(
                            type_hierarchy.iter().map(|t| t.to_string()).collect()
                        )
                    )
                    .as_str(),
                )
                .with_hint("considering using reference types instead"),
            );
        }

        ctx.add_struct(rich_struct.clone());
        rich_struct
    }

    /// Recursively checks for struct containment cycles that would imply struct types with infinite
    /// size.
    pub fn analyze_containment(
        ctx: &ProgramContext,
        struct_type: &StructType,
    ) -> AnalyzeResult<()> {
        RichStruct::check_containment_cycles(ctx, struct_type, &mut vec![])
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
                            format!(
                                "type `{}` cannot contain itself (via field `{}` on struct type \
                                `{}`)",
                                format!("{}", unresolved_type.name).blue(),
                                format!("{}", field.name).blue(),
                                format!("{}", struct_type).blue(),
                            )
                            .as_str(),
                            Box::new(field.clone()),
                        )
                        .with_detail(
                            format!(
                                "the offending type hierarchy is {}",
                                RichType::hierarchy_to_string(hierarchy.clone())
                            )
                            .as_str(),
                        )
                        .with_hint(
                            format!(
                                "consider changing field `{}: {}` to `{}: &{}`",
                                field.name.blue(),
                                unresolved_type.name.blue(),
                                field.name.blue(),
                                unresolved_type.name.blue()
                            )
                            .as_str(),
                        ));
                    }

                    let field_struct_type = ctx
                        .get_extern_struct(unresolved_type.name.as_str())
                        .unwrap();
                    RichStruct::check_containment_cycles(ctx, field_struct_type, hierarchy)?;
                    hierarchy.pop();
                }

                Type::Struct(field_struct_type) => {
                    if !field_struct_type.name.is_empty()
                        && hierarchy.contains(&field_struct_type.name)
                    {
                        return Err(AnalyzeError::new_with_locatable(
                            ErrorKind::InfiniteSizedType,
                            format!(
                                "type `{}` cannot contain itself (via struct field `{}` on struct \
                                type `{}`)",
                                field_struct_type.name.blue(),
                                field.name.blue(),
                                struct_type.name.blue(),
                            )
                            .as_str(),
                            Box::new(field.clone()),
                        )
                        .with_hint(
                            format!(
                                "consider changing field `{}: {}` to `{}: &{}`",
                                field.name.blue(),
                                format!("{}", field_struct_type).blue(),
                                field.name.blue(),
                                format!("{}", field_struct_type).blue()
                            )
                            .as_str(),
                        ));
                    }

                    hierarchy.push(field_struct_type.name.clone());
                    RichStruct::check_containment_cycles(ctx, field_struct_type, hierarchy)?;
                    hierarchy.pop();
                }

                Type::I64(_) | Type::String(_) | Type::Bool(_) | Type::Function(_) => {}
            }
        }

        Ok(())
    }

    /// Returns the type of the struct field with the given name.
    fn get_field_type(&self, name: &str) -> Option<&RichType> {
        for field in &self.fields {
            if field.name.as_str() == name {
                return Some(&field.typ);
            }
        }

        None
    }
}

/// Represents a semantically valid struct initialization.
#[derive(Debug, Clone)]
pub struct RichStructInit {
    pub typ: RichStruct,
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
        let struct_type = match RichType::from(ctx, &struct_init.typ) {
            RichType::Struct(s) => s,
            RichType::Unknown(type_name) => {
                // The struct type has already failed semantic analysis, so we should avoid
                // analyzing its initialization and just return some zero-value placeholder instead.
                return RichStructInit {
                    typ: RichStruct {
                        name: type_name,
                        fields: vec![],
                    },
                    field_values: Default::default(),
                };
            }
            other => {
                panic!("found invalid struct type {}", other);
            }
        };

        // Analyze struct field assignments.
        let mut field_values: HashMap<String, RichExpr> = HashMap::new();
        for (field_name, field_value) in &struct_init.field_values {
            // Get the struct field type, or error if the struct type has no such field.
            let field_type = match struct_type.get_field_type(field_name.as_str()) {
                Some(typ) => typ,
                None => {
                    ctx.add_err(AnalyzeError::new_with_locatable(
                        ErrorKind::StructFieldNotDefined,
                        format!(
                            "struct type `{}` has no field `{}`",
                            format!("{}", struct_type).blue(),
                            format!("{}", field_name).blue(),
                        )
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
            if !expr.typ.is_compatible_with(field_type) {
                ctx.add_err(AnalyzeError::new_with_locatable(
                    ErrorKind::IncompatibleTypes,
                    format!(
                        "cannot assign expression of type `{}` to field `{}: {}` on struct type \
                        `{}`",
                        format!("{}", &expr.typ).blue(),
                        format!("{}", &field_name).blue(),
                        format!("{}", &field_type).blue(),
                        format!("{}", &struct_type).blue(),
                    )
                    .as_str(),
                    Box::new(field_value.clone()),
                ));
            }

            // Insert the analyzed struct field value, making sure that it was not already assigned.
            if field_values.insert(field_name.to_string(), expr).is_some() {
                ctx.add_err(AnalyzeError::new_with_locatable(
                    ErrorKind::DuplicateStructFieldName,
                    format!("struct field `{}` is already assigned", &field_name.blue()).as_str(),
                    Box::new(field_value.clone()),
                ));
            }
        }

        // Make sure all struct fields were assigned.
        for field in &struct_type.fields {
            if !field_values.contains_key(field.name.as_str()) {
                ctx.add_err(AnalyzeError::new_with_locatable(
                    ErrorKind::StructFieldNotInitialized,
                    format!(
                        "field `{}` on struct type `{}` is uninitialized",
                        format!("{}", field.name).blue(),
                        format!("{}", struct_type).blue(),
                    )
                    .as_str(),
                    Box::new(struct_init.clone()),
                ));
            }
        }

        RichStructInit {
            typ: struct_type,
            field_values,
        }
    }
}
