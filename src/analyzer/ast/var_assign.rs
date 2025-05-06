use core::fmt;
use std::fmt::Formatter;

use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{
    err_assign_to_const, err_assign_to_immut_var, err_assign_to_non_var, err_assign_via_immut_ptr,
};
use crate::analyzer::ident::{IdentKind, Usage};
use crate::analyzer::prog_context::ProgramContext;
use crate::lexer::pos::{Locatable, Span};
use crate::parser::ast::op::Operator;
use crate::parser::ast::var_assign::VariableAssignment;

/// Represents a semantically valid and type-rich variable assignment.
#[derive(Clone, PartialEq, Debug)]
pub struct AVarAssign {
    pub target: AExpr,
    pub val: AExpr,
    pub span: Span,
}

impl fmt::Display for AVarAssign {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.target, self.val)
    }
}

impl AVarAssign {
    /// Performs semantic analysis on the given variable assignment and returns a type-rich version
    /// of it.
    pub fn from(ctx: &mut ProgramContext, assign: &VariableAssignment) -> Self {
        // Analyze the expression representing the target value of the assignment.
        let target = AExpr::from(ctx, assign.target.clone(), None, false, false);

        // Check that we can actually assign to the target (it must be a mutable variable, or
        // it must be writing to memory via a `*mut _`). We skip this check if the target
        // expression already failed analysis. If the target turns out not to be
        // assignable, we'll skip type checks for the assigned expression to avoid
        // redundant errors.
        let maybe_expected_right_type_key = match !ctx.get_type(target.type_key).is_unknown()
            && check_assignable(ctx, assign.span(), &target)
        {
            true => Some(target.type_key),
            false => None,
        };

        // Analyze the expression representing the value assigned to the variable.
        let a_expr = AExpr::from(
            ctx,
            assign.value.clone(),
            maybe_expected_right_type_key,
            false,
            false,
        );

        AVarAssign {
            target,
            val: a_expr,
            span: assign.span,
        }
    }
}

/// Checks if the given `target_expr` can be assigned to and inserts an error into the program context
/// if not. Only mutable variables (and their members/elements) and dereferenced `*mut _` pointers can be
/// assigned to. Returns true if the target is assignable and false otherwise.
fn check_assignable(ctx: &mut ProgramContext, span: &Span, target_expr: &AExpr) -> bool {
    match &target_expr.kind {
        // We're just assigning to a variable. Make sure it's mutable.
        AExprKind::Symbol(symbol) => {
            if symbol.is_null_intrinsic() {
                let err = err_assign_to_non_var(ctx, &target_expr.kind, *span);
                ctx.insert_err(err);
                return false;
            }

            let ident = match ctx.get_local_ident(&symbol.name, Some(Usage::Write)) {
                Some(v) => v,
                None => {
                    return true;
                }
            };

            match &ident.kind {
                IdentKind::Const { .. } => {
                    let err = err_assign_to_const(ctx, target_expr, &symbol.name, *span);
                    ctx.insert_err(err);
                    return false;
                }

                IdentKind::Variable { is_mut: false, .. }
                | IdentKind::Static { is_mut: false, .. } => {
                    let err = err_assign_to_immut_var(ctx, target_expr, &symbol.name, *span);
                    ctx.insert_err(err);
                    return false;
                }

                _ => {}
            }

            true
        }

        // We're assigning to a value via a pointer. Make sure the pointer is `*mut`.
        AExprKind::UnaryOperation(Operator::Defererence, operand) => {
            if let AType::Pointer(ptr_type) = ctx.get_type(operand.type_key) {
                if !ptr_type.is_mut {
                    let err = err_assign_via_immut_ptr(ctx, ptr_type, operand, *span);
                    ctx.insert_err(err);
                    return false;
                }
            }

            true
        }

        // We're assigning to a field on a struct or tuple. Make sure the base variable is mutable.
        AExprKind::MemberAccess(access) => check_assignable(ctx, span, &access.base_expr),

        // We're assigning to a slot in an array. Make sure the array is mutable.
        AExprKind::Index(index) => check_assignable(ctx, span, &index.collection_expr),

        // Cannot assign to other types of expressions because they're not variables.
        other => {
            let err = err_assign_to_non_var(ctx, other, *span);
            ctx.insert_err(err);
            false
        }
    }
}
