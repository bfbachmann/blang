use colored::Colorize;
use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::{Locatable, Position};
use crate::locatable_impl;
use crate::parser::ast::index::Index;
use crate::parser::ast::r#type::Type;

/// Represents the access of some value at a specific index in a collection.
#[derive(Clone, Debug, PartialEq)]
pub struct AIndex {
    pub collection_expr: AExpr,
    pub index_expr: AExpr,
    pub result_type_key: TypeKey,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(AIndex);

impl Display for AIndex {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}[{}]", self.collection_expr, self.index_expr)
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
            index_expr: AExpr::new_zero_value(ctx, Type::new_unresolved("u64")),
            result_type_key: ctx.unknown_type_key(),
            start_pos: index.start_pos().clone(),
            end_pos: index.end_pos().clone(),
        };

        // For now, we'll require that the expression if of some array type.
        let collection_type = ctx.must_get_type(collection_expr.type_key);
        let (result_type_key, array_len) = match collection_type {
            AType::Unknown(_) => {
                // The collection expression already failed analysis, so we can
                // just return early.
                return placeholder;
            }

            AType::Array(array_type) => match array_type.maybe_element_type_key {
                Some(tk) => (tk, array_type.len),
                None => {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::IndexOutOfBounds,
                        "cannot index zero-length array",
                        index,
                    ));

                    return placeholder;
                }
            },

            other => {
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::MismatchedTypes,
                    format_code!("cannot index value of type {}", other.display(ctx)).as_str(),
                    &index.index_expr,
                ));

                return placeholder;
            }
        };

        // Analyze the index expression. It should be of type `u64`.
        let index_expr = AExpr::from(
            ctx,
            index.index_expr.clone(),
            Some(ctx.u64_type_key()),
            false,
            false,
        );

        // If the index is a constant, we can check if it's in-bounds.
        match index_expr.try_into_const_u64(ctx) {
            Ok(i) if i >= array_len => {
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::IndexOutOfBounds,
                    format!(
                        "index ({}) is outside of array bounds ([0:{}])",
                        i,
                        array_len - 1
                    )
                    .as_str(),
                    index,
                ));

                placeholder
            }
            _ => AIndex {
                collection_expr,
                index_expr,
                result_type_key,
                start_pos: index.start_pos().clone(),
                end_pos: index.end_pos().clone(),
            },
        }
    }

    /// Returns a string containing the human-readable version of this index expression.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        format!(
            "{}[{}]",
            self.collection_expr.display(ctx),
            self.index_expr.display(ctx)
        )
    }
}
