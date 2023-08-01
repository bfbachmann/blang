use std::collections::{HashSet};
use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::RichType;
use crate::analyzer::AnalyzeResult;
use crate::parser::r#struct::Struct;
use crate::parser::r#type::Type;

/// Represents a semantically valid and type-rich struct field.
#[derive(Clone, Debug)]
pub struct RichField {
    pub name: String,
    pub typ: RichType,
}

impl fmt::Display for RichField {
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

impl fmt::Display for RichStruct {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "struct {} {{", self.name)?;

        if !self.fields.is_empty() {
            for field in &self.fields {
                write!(f, "{}", field)?;
            }
        }

        return write!(f, "}}");
    }
}

impl PartialEq for RichStruct {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl RichStruct {
    /// Performs semantic analysis on a struct type declaration. Note that this will also
    /// recursively analyze any types contained in the struct. On success, the struct type info will
    /// be stored in the program context.
    pub fn from(ctx: &mut ProgramContext, struct_type: &Struct) -> AnalyzeResult<Self> {
        // Check if the struct type is already defined in the program context. This will be the case
        // if we've already analyzed it in the process of analyzing another type that contains
        // this type.
        if let Some(rich_struct) = ctx.get_struct(struct_type.name.as_str()) {
            return Ok(rich_struct.clone());
        }

        // Analyze the struct fields
        let mut fields = vec![];
        let mut field_names = HashSet::new();
        for field in &struct_type.fields {
            // Check for duplicated field name.
            if !field_names.insert(field.name.clone()) {
                return Err(AnalyzeError::new(
                    ErrorKind::DuplicateStructFieldName,
                    format!(
                        "struct type {} cannot have multiple fields named {}",
                        struct_type.name, field.name,
                    )
                    .as_str(),
                ));
            }

            // Make sure the struct field type is not the same as this struct type to prevent
            // containment cycles causing types of infinite size.
            if let Type::Unresolved(field_type_name) = &field.typ {
                if field_type_name == &struct_type.name {
                    return Err(AnalyzeError::new(
                        ErrorKind::ContainmentCycle,
                        format!(
                            "struct {} cannot directly contain itself (at field {})",
                            struct_type.name, field_type_name
                        )
                        .as_str(),
                    ));
                }
            }

            // Resolve the struct field type.
            let struct_field_type = RichType::from(ctx, &field.typ)?;
            fields.push(RichField {
                name: field.name.clone(),
                typ: struct_field_type,
            });
        }

        let rich_struct = RichStruct {
            name: struct_type.name.clone(),
            fields,
        };

        // Make sure the struct doesn't contain itself via other types.
        let rich_struct_type = RichType::Struct(rich_struct.clone());
        if rich_struct_type.contains_type(&rich_struct_type) {
            return Err(AnalyzeError::new(
                ErrorKind::ContainmentCycle,
                format!(
                    "struct {} cannot contain itself via any of its field types",
                    rich_struct.name
                )
                .as_str(),
            ));
        }

        ctx.add_struct(rich_struct.clone());
        Ok(rich_struct)
    }
}

/// Recursively checks for struct containment cycles that would imply struct types with infinite
/// size.
pub fn analyze_struct_containment(ctx: &ProgramContext, struct_type: &Struct) -> AnalyzeResult<()> {
    check_containment_cycles(ctx, struct_type, &mut vec![])
}

fn check_containment_cycles(
    ctx: &ProgramContext,
    struct_type: &Struct,
    hierarchy: &mut Vec<String>,
) -> AnalyzeResult<()> {
    hierarchy.push(struct_type.name.clone());

    for field in &struct_type.fields {
        match &field.typ {
            Type::Unresolved(field_type_name) => {
                if hierarchy.contains(field_type_name) {
                    return Err(AnalyzeError::new(
                        ErrorKind::ContainmentCycle,
                        format!(
                            "type {} cannot contain itself (via field {} on struct type {})",
                            field_type_name, field.name, struct_type.name,
                        )
                        .as_str(),
                    ));
                }

                hierarchy.push(field_type_name.to_string());
                let field_struct_type = ctx.get_extern_struct(field_type_name.as_str()).unwrap();
                check_containment_cycles(ctx, field_struct_type, hierarchy)?;
                hierarchy.pop();
            }
            Type::Struct(field_struct_type) => {
                if !field_struct_type.name.is_empty() && hierarchy.contains(&field_struct_type.name)
                {
                    return Err(AnalyzeError::new(
                        ErrorKind::ContainmentCycle,
                        format!(
                            "type {} cannot contain itself (via struct field {} on struct type {})",
                            field_struct_type.name, field.name, struct_type.name,
                        )
                        .as_str(),
                    ));
                }

                hierarchy.push(field_struct_type.name.clone());
                check_containment_cycles(ctx, field_struct_type, hierarchy)?;
                hierarchy.pop();
            }
            Type::I64 | Type::String | Type::Bool | Type::Function(_) => {}
        }
    }

    Ok(())
}
