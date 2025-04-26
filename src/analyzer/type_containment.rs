use crate::analyzer::error::{AnalyzeError, AnalyzeResult, ErrorKind};
use crate::analyzer::ident::IdentKind;
use crate::analyzer::prog_context::ProgramContext;
use crate::fmt::hierarchy_to_string;
use crate::lexer::pos::Span;
use crate::parser::ast::array::ArrayType;
use crate::parser::ast::r#enum::EnumType;
use crate::parser::ast::r#struct::StructType;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::tuple::TupleType;

/// Analyzes type containment and returns an error if there are any illegal type containment cycles
/// that would result in infinite-sized types.
pub fn check_type_containment(
    ctx: &ProgramContext,
    typ: &Type,
    hierarchy: &mut Vec<String>,
) -> AnalyzeResult<()> {
    match typ {
        Type::Unresolved(unresolved_type) => {
            if let Some(ident) = ctx.get_local_ident_unchecked(&unresolved_type.name) {
                match &ident.kind {
                    IdentKind::UncheckedStructType(struct_type) => {
                        check_struct_containment(ctx, struct_type, hierarchy)?;
                    }
                    IdentKind::UncheckedEnumType(enum_type) => {
                        check_enum_containment(ctx, enum_type, hierarchy)?;
                    }
                    _ => {}
                }
            }
        }

        Type::Tuple(field_tuple_type) => {
            check_tuple_containment(ctx, field_tuple_type, hierarchy)?;
        }

        Type::Array(array_type) => {
            check_array_containment(ctx, array_type, hierarchy)?;
        }

        // These types can't have illegal containment cycles.
        Type::Function(_) | Type::Pointer(_) => {}
    }

    Ok(())
}

/// Analyzes type containment within the given struct type and returns an error if there are any
/// illegal type containment cycles that would result in infinite-sized types.
pub fn check_struct_containment(
    ctx: &ProgramContext,
    struct_type: &StructType,
    hierarchy: &mut Vec<String>,
) -> AnalyzeResult<()> {
    if hierarchy.contains(&struct_type.name) {
        return Err(new_containment_err(
            struct_type.name.as_str(),
            hierarchy,
            struct_type.span,
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

/// Analyzes type containment within the given enum type and returns an error if there are any
/// illegal type containment cycles that would result in infinite-sized types.
pub fn check_enum_containment(
    ctx: &ProgramContext,
    enum_type: &EnumType,
    hierarchy: &mut Vec<String>,
) -> AnalyzeResult<()> {
    if hierarchy.contains(&enum_type.name) {
        return Err(new_containment_err(
            enum_type.name.as_str(),
            hierarchy,
            enum_type.span,
        ));
    }

    // Push this type name onto the hierarchy stack so it can be checked against other types.
    hierarchy.push(enum_type.name.clone());

    // Recursively check each enum variant type.
    for variant in &enum_type.variants {
        if let Some(typ) = &variant.maybe_type {
            check_type_containment(ctx, typ, hierarchy)?;
        }
    }

    // Pop this type name off the hierarchy stack because all types it contains have been
    // checked.
    hierarchy.pop();

    Ok(())
}

/// Analyzes type containment within the given tuple type and returns an error if there are any
/// illegal type containment cycles that would result in infinite-sized types.
pub fn check_tuple_containment(
    ctx: &ProgramContext,
    tuple_type: &TupleType,
    hierarchy: &mut Vec<String>,
) -> AnalyzeResult<()> {
    // Recursively check each tuple field type.
    for typ in &tuple_type.field_types {
        check_type_containment(ctx, &typ, hierarchy)?;
    }

    Ok(())
}

/// Analyzes type containment within the given array type and returns an error if there are any
/// illegal type containment cycles that would result in infinite-size types.
pub fn check_array_containment(
    ctx: &ProgramContext,
    array_type: &ArrayType,
    hierarchy: &mut Vec<String>,
) -> AnalyzeResult<()> {
    if let Some(typ) = &array_type.maybe_element_type {
        check_type_containment(ctx, typ, hierarchy)
    } else {
        Ok(())
    }
}

fn new_containment_err(type_name: &str, hierarchy: &Vec<String>, span: Span) -> AnalyzeError {
    AnalyzeError::new(
        ErrorKind::InfiniteSizedType,
        format_code!("type {} cannot contain itself", type_name).as_str(),
        span,
    )
    .with_detail(
        format!(
            "The offending type hierarchy is {}.",
            hierarchy_to_string(hierarchy)
        )
        .as_str(),
    )
    .with_help(
        "Consider adding some form of indirection on the offending types, like a pointer type.",
    )
}
