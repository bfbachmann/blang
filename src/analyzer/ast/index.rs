use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{
    err_cannot_index_value, err_index_empty_array, err_index_out_of_bounds,
    err_mismatched_index_type,
};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::Span;
use crate::locatable_impl;
use crate::parser::ast::index::Index;
use crate::parser::ast::r#type::Type;
use crate::Locatable;

/// Represents the access of some value at a specific index in a collection.
/// The collection can either be an array, a tuple, or a pointer. If it is a
/// pointer, the index expression represents calculating an offset from the
/// pointer (a GEP, essentially).
#[derive(Clone, Debug, PartialEq)]
pub struct AIndex {
    pub collection_expr: AExpr,
    pub index_expr: AExpr,
    pub result_type_key: TypeKey,
    pub span: Span,
}

locatable_impl!(AIndex);

impl Display for AIndex {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.({})", self.collection_expr, self.index_expr)
    }
}

impl AIndex {
    /// Performs semantic analysis on an index expression.
    pub fn from(ctx: &mut ProgramContext, index: &Index) -> AIndex {
        // Analyze the value being indexed.
        let collection_expr = AExpr::from(ctx, index.collection_expr.clone(), None, false, false);

        // This value will serve as a placeholder for when we error.
        let placeholder = AIndex {
            collection_expr: collection_expr.clone(),
            index_expr: AExpr::new_zero_value(ctx, Type::new_unresolved("uint")),
            result_type_key: ctx.unknown_type_key(),
            span: *index.span(),
        };

        // The collection expression must be of an array, tuple, or pointer type.
        let collection_type = ctx.get_type(collection_expr.type_key);
        let (maybe_collection_len, mut result_type_key, is_tuple) = match collection_type {
            AType::Array(array_type) => match array_type.maybe_element_type_key {
                Some(elem_tk) => (Some(array_type.len), elem_tk, false),

                None => {
                    ctx.insert_err(err_index_empty_array(index.span));
                    return placeholder;
                }
            },

            // We'll figure out what the result type is after we analyze the index
            // expression.
            AType::Tuple(tuple_type) => (
                Some(tuple_type.fields.len() as u64),
                ctx.unknown_type_key(),
                true,
            ),

            AType::Pointer(_) => (None, collection_expr.type_key, false),

            AType::Unknown(_) => {
                // The collection expression already failed analysis, so we can
                // just return early.
                return placeholder;
            }

            _ => {
                let err =
                    err_cannot_index_value(ctx, collection_expr.type_key, *index.index_expr.span());
                ctx.insert_err(err);
                return placeholder;
            }
        };

        // Analyze the index expression based on whether we're indexing an array,
        // a tuple, or a pointer. Arrays and tuples have `uint` indices, whereas
        // pointers have `int` indices.
        let index_expr = if let Some(len) = maybe_collection_len {
            // Analyze the index expression. It should be of type `uint`.
            let index_expr = AExpr::from(
                ctx,
                index.index_expr.clone(),
                Some(ctx.uint_type_key()),
                false,
                false,
            );

            // If the index expression is constant, we can perform
            // bounds checking at compile time.
            if let Some(i) = index_expr.try_into_const_uint(ctx) {
                if i >= len {
                    let err = err_index_out_of_bounds(i, len, *index.index_expr.span());
                    ctx.insert_err(err);
                    return placeholder;
                }

                // If the collection is a tuple, set the result type to the type
                // of the tuple field at the specified index.
                if let AType::Tuple(tuple_type) = ctx.get_type(collection_expr.type_key) {
                    result_type_key = tuple_type.get_field_type_key(i as usize).unwrap();
                }
            } else if is_tuple {
                // At this point we know we're indexing a tuple with a value
                // that is not constant and/or not a `uint`, which is illegal.
                let err = err_mismatched_index_type(
                    ctx,
                    index_expr.kind.is_const(),
                    index_expr.type_key,
                    *index.index_expr.span(),
                );
                ctx.insert_err(err);

                return placeholder;
            };

            index_expr
        } else {
            // At this point we know a pointer is being indexed, so we can
            // just analyze the index expression expecting type `int`.
            AExpr::from(
                ctx,
                index.index_expr.clone(),
                Some(ctx.int_type_key()),
                false,
                false,
            )
        };

        AIndex {
            collection_expr,
            index_expr,
            result_type_key,
            span: *index.span(),
        }
    }

    /// Returns a string containing the human-readable version of this index expression.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        format!(
            "{}.({})",
            self.collection_expr.display(ctx),
            self.index_expr.display(ctx)
        )
    }
}
