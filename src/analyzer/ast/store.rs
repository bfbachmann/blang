use colored::Colorize;
use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::pointer::APointerType;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::parser::store::Store;

/// Represents a store operation (writing a value to memory addressed by a pointer).
#[derive(Clone, Debug, PartialEq)]
pub struct AStore {
    pub source_expr: AExpr,
    pub dest_expr: AExpr,
}

impl Display for AStore {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} <- {}", self.dest_expr, self.source_expr)
    }
}

impl AStore {
    /// Performs semantic analysis on the given store statement.
    pub fn from(ctx: &mut ProgramContext, store: &Store) -> AStore {
        // Analyze the destination expression.
        let dest_expr = AExpr::from(ctx, store.dest_expr.clone(), None, false);

        // Make sure the destination expression has a pointer type.
        let maybe_dest_pointee_tk = match ctx.must_get_type(dest_expr.type_key) {
            AType::Pointer(APointerType { pointee_type_key }) => Some(*pointee_type_key),
            other => {
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::MismatchedTypes,
                    format_code!(
                        "expected store destination to have pointer type ({}), but found type {}",
                        "*_",
                        other
                    )
                    .as_str(),
                    &store.dest_expr,
                ));

                None
            }
        };

        // Analyze the source expression.
        let source_expr = AExpr::from(ctx, store.source_expr.clone(), maybe_dest_pointee_tk, false);

        AStore {
            source_expr,
            dest_expr,
        }
    }
}
