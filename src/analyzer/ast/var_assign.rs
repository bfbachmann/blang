use core::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::format_code;
use crate::parser::ast::op::Operator;
use crate::parser::ast::var_assign::VariableAssignment;

/// Represents a semantically valid and type-rich variable assignment.
#[derive(Clone, PartialEq, Debug)]
pub struct AVarAssign {
    pub target: AExpr,
    pub val: AExpr,
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
        // expression already failed analysis.
        if !ctx.must_get_type(target.type_key).is_unknown() {
            check_mutablility(ctx, assign, &target);
        }

        // Analyze the expression representing the value assigned to the variable.
        let a_expr = AExpr::from(
            ctx,
            assign.value.clone(),
            Some(target.type_key),
            false,
            false,
        );

        AVarAssign {
            target,
            val: a_expr,
        }
    }
}

/// Checks if the given `target_expr` can be assigned to and inserts an error into the program context
/// if not. Only mutable variables (and their members/elements) and dereferenced `*mut _` pointers can be
/// assigned to.
fn check_mutablility(ctx: &mut ProgramContext, assign: &VariableAssignment, target_expr: &AExpr) {
    match &target_expr.kind {
        // We're just assigning to a variable. Make sure it's mutable.
        AExprKind::Symbol(symbol) => {
            let var = match ctx.get_symbol(symbol.name.as_str()) {
                Some(v) => v,
                None => {
                    // The variable does not exist. Record the error and skip any further checks.
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::UndefSymbol,
                        format_code!("cannot assign to undefined variable {}", &symbol.name)
                            .as_str(),
                        assign,
                    ));

                    return;
                }
            };

            if var.is_const {
                ctx.insert_err(
                    AnalyzeError::new(
                        ErrorKind::ImmutableAssignment,
                        format_code!("cannot assign to constant {}", target_expr.display(ctx))
                            .as_str(),
                        assign,
                    )
                    .with_help(
                        format_code!(
                            "Consider declaring {} as a mutable local variable.",
                            &symbol.name
                        )
                        .as_str(),
                    ),
                );
            } else if !var.is_mut {
                ctx.insert_err(
                    AnalyzeError::new(
                        ErrorKind::ImmutableAssignment,
                        format_code!(
                            "cannot assign to immutable variable {}",
                            target_expr.display(ctx)
                        )
                        .as_str(),
                        assign,
                    )
                    .with_help(
                        format_code!("Consider declaring {} as mutable.", &symbol.name).as_str(),
                    ),
                );
            }
        }

        // We're assigning to a value via a pointer. Make sure the pointer is `*mut`.
        AExprKind::UnaryOperation(Operator::Defererence, operand) => {
            if let AType::Pointer(pointer_type) = ctx.must_get_type(operand.type_key) {
                if !pointer_type.is_mut {
                    let pointee_type = ctx.must_get_type(pointer_type.pointee_type_key);
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::ImmutableAssignment,
                        format_code!(
                            "cannot assign to immutable variable {}",
                            target_expr.display(ctx)
                        )
                        .as_str(),
                        assign,
                    ).with_detail(
                        format_code!(
                            "Cannot assign via a pointer of type {} that points to an immutable value.",
                            pointer_type.display(ctx),
                        ).as_str()
                    ).with_help(
                        format_code!(
                            "For this assignment to work, {} would need to have type {}.",
                            operand.display(ctx),
                            format!("*mut {}", pointee_type.display(ctx)),
                        ).as_str()
                    ));
                }
            }
        }

        // We're assigning to a field on a struct or tuple. Make sure the base variable is mutable.
        AExprKind::MemberAccess(access) => check_mutablility(ctx, assign, &access.base_expr),

        // We're assigning to a slot in an array. Make sure the array is mutable.
        AExprKind::Index(index) => check_mutablility(ctx, assign, &index.collection_expr),

        // Cannot assign to other types of expressions because they're not variables.
        other => {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::InvalidAssignmentTarget,
                format_code!("cannot assign to non-variable {}", other.display(ctx)).as_str(),
                assign,
            ));
        }
    }
}
