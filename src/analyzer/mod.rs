use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{
    err_mismatched_types, err_spec_not_satisfied, AnalyzeResult, ErrorKind,
};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::Locatable;
use std::collections::HashMap;

pub mod analyze;
pub mod ast;
pub mod error;
pub mod ident;
pub mod mangling;
pub mod mod_context;
pub mod prog_context;
pub mod scope;
mod tests;
mod type_containment;
pub mod type_store;
pub mod warn;

/// Tries to check if the actual type matches the expected type using the provided type mappings.
/// Updates the mappings if the actual type is compatible with the expected type and the expected
/// type is not already mapped.
/// Basically, this function is trying to figure out if some type is valid as an argument to a
/// generic function without necessarily knowing which monomorphization of that generic function
/// is required, and then updating the type mappings for the generic function if the argument is
/// valid and "resolves" a generic parameter type.
pub fn check_types(
    ctx: &mut ProgramContext,
    expected_tk: TypeKey,
    actual_tk: TypeKey,
    type_mappings: &mut HashMap<TypeKey, TypeKey>,
    loc: &impl Locatable,
) -> AnalyzeResult<()> {
    // Nothing to do if the actual type has already failed analysis.
    let unknown_tk = ctx.unknown_type_key();
    if actual_tk == unknown_tk || expected_tk == unknown_tk {
        return Ok(());
    }

    // If the expected type key is already mapped to another type, it means we've resolved that
    // generic parameter type to another type, so we should check against that other type instead.
    let (already_mapped, mut mapped_expected_tk) = match type_mappings.get(&expected_tk) {
        Some(existing_tk) if *existing_tk != ctx.unknown_type_key() => (true, *existing_tk),
        _ => (false, expected_tk),
    };

    // Maybe we can find and replace already-mapped generic types in the expected type and just
    // compare that resulting type with the actual type.
    {
        let type_mappings = HashMap::from_iter(type_mappings.iter().filter_map(|(k, v)| {
            match *v == ctx.unknown_type_key() {
                true => None,
                false => Some((*k, *v)),
            }
        }));
        if !type_mappings.is_empty() {
            ctx.replace_tks(&mut mapped_expected_tk, &type_mappings);
        }
    }

    let mismatched_types_err =
        err_mismatched_types(ctx, mapped_expected_tk, actual_tk, *loc.span());

    // Do some simple checks to see if the types are the same.
    if ctx.types_match(mapped_expected_tk, actual_tk, false) {
        return Ok(());
    }

    // At this point we know the types aren't the same. If the expected argument type was already
    // mapped to another type, then the actual type for sure is not a match at this point.
    if already_mapped {
        return Err(mismatched_types_err);
    }

    // At this point we know that the expected type is some generic type that we have not yet
    // mapped to a type, so we'll try to do that now.
    let expected_type = ctx.get_type(mapped_expected_tk);
    let actual_type = ctx.get_type(actual_tk);
    match (expected_type.clone(), actual_type.clone()) {
        (AType::Pointer(expected_ptr_type), AType::Pointer(actual_ptr_type)) => {
            return check_types(
                ctx,
                expected_ptr_type.pointee_type_key,
                actual_ptr_type.pointee_type_key,
                type_mappings,
                loc,
            )
        }

        (AType::Array(expected_array_type), AType::Array(actual_array_type)) => {
            return match (
                expected_array_type.maybe_element_type_key,
                actual_array_type.maybe_element_type_key,
            ) {
                (Some(expected_tk), Some(actual_tk))
                    if expected_array_type.len == actual_array_type.len =>
                {
                    check_types(ctx, expected_tk, actual_tk, type_mappings, loc)
                }
                _ => Err(mismatched_types_err),
            }
        }

        (AType::Tuple(expected_tuple_type), AType::Tuple(actual_tuple_type)) => {
            if expected_tuple_type.fields.len() != actual_tuple_type.fields.len() {
                return Err(mismatched_types_err);
            }

            for (expected_field, actual_field) in expected_tuple_type
                .fields
                .iter()
                .zip(actual_tuple_type.fields.iter())
            {
                check_types(
                    ctx,
                    expected_field.type_key,
                    actual_field.type_key,
                    type_mappings,
                    loc,
                )?
            }

            return Ok(());
        }

        (AType::Struct(_), AType::Struct(_)) | (AType::Enum(_), AType::Enum(_)) => {
            let expected_mono = ctx.type_monomorphizations.get(&mapped_expected_tk);
            let actual_mono = ctx.type_monomorphizations.get(&actual_tk);

            return match (expected_mono, actual_mono) {
                (Some(expected_mono), Some(actual_mono)) => {
                    if expected_mono.poly_type_key != actual_mono.poly_type_key {
                        return Err(mismatched_types_err);
                    }

                    let expected_type_mappings = expected_mono.type_mappings();
                    let actual_type_mappings = actual_mono.type_mappings();

                    for (generic_tk, replacement_tk) in expected_type_mappings {
                        let actual_tk = actual_type_mappings.get(&generic_tk).unwrap();
                        check_types(ctx, replacement_tk, *actual_tk, type_mappings, loc)?
                    }

                    Ok(())
                }

                _ => Err(mismatched_types_err),
            };
        }

        (AType::Function(expected_sig), AType::Function(actual_sig)) => {
            match (
                &expected_sig.maybe_ret_type_key,
                &actual_sig.maybe_ret_type_key,
            ) {
                (Some(expected_ret_tk), Some(actual_ret_tk)) => {
                    match check_types(ctx, *expected_ret_tk, *actual_ret_tk, type_mappings, loc) {
                        // Return the type mismatch error with the outer types rather than the
                        // inner types.
                        Err(err) if err.kind == ErrorKind::MismatchedTypes => {
                            return Err(mismatched_types_err);
                        }
                        Err(err) => {
                            return Err(err);
                        }
                        _ => {}
                    }
                }

                (None, None) => {}

                _ => {
                    return Err(mismatched_types_err);
                }
            }

            if expected_sig.args.len() != actual_sig.args.len() {
                return Err(mismatched_types_err);
            }

            for (expected_arg, actual_arg) in expected_sig.args.iter().zip(actual_sig.args) {
                match check_types(
                    ctx,
                    expected_arg.type_key,
                    actual_arg.type_key,
                    type_mappings,
                    loc,
                ) {
                    // Return the type mismatch error with the outer types rather than the
                    // inner types.
                    Err(err) if err.kind == ErrorKind::MismatchedTypes => {
                        return Err(mismatched_types_err);
                    }
                    Err(err) => {
                        return Err(err);
                    }
                    _ => {}
                }
            }

            return Ok(());
        }

        (AType::Generic(_), _) => {
            // Check if we can safely map the actual type to the expected parameter type below.
        }

        _ => {
            // At this point we know the expected type is not generic, and it for sure doesn't
            // match the actual type, so it must be a type mismatch.
            return Err(mismatched_types_err);
        }
    };

    // Make sure the actual type satisfies the generic constraints.
    let expected_param = expected_type.to_generic_type();
    let param_name = expected_param.name.clone();
    let parent_tk = expected_param.poly_type_key;
    let missing_spec_tks = ctx.get_missing_spec_impls(actual_tk, mapped_expected_tk);
    let missing_spec_names: Vec<String> = missing_spec_tks
        .into_iter()
        .map(|tk| ctx.display_type(tk))
        .collect();
    if !missing_spec_names.is_empty() {
        let err = err_spec_not_satisfied(
            ctx,
            actual_tk,
            &missing_spec_names,
            &param_name,
            parent_tk,
            *loc.span(),
        );
        return Err(err);
    }

    // We can safely map the expected generic type to the actual type.
    type_mappings.insert(expected_tk, actual_tk);
    Ok(())
}
