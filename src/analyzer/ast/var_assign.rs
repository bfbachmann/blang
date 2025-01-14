use core::fmt;
use std::fmt::Formatter;

use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::format_code;
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
            && check_assignable(ctx, assign, &target)
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
fn check_assignable<T: Locatable>(ctx: &mut ProgramContext, loc: &T, target_expr: &AExpr) -> bool {
    match &target_expr.kind {
        // We're just assigning to a variable. Make sure it's mutable.
        AExprKind::Symbol(symbol) => {
            if symbol.is_null_intrinsic() {
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::InvalidAssignmentTarget,
                    format_code!("cannot assign to intrinsic {}", &symbol.name).as_str(),
                    loc,
                ));

                return false;
            }

            let var = match ctx.get_scoped_symbol(None, symbol.name.as_str()) {
                Some(v) => v,
                None => {
                    // The variable does not exist. Record the error and skip any further checks.
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::UndefSymbol,
                        format_code!("cannot assign to undefined variable {}", &symbol.name)
                            .as_str(),
                        loc,
                    ));

                    return false;
                }
            };

            if var.is_const {
                ctx.insert_err(
                    AnalyzeError::new(
                        ErrorKind::ImmutableAssignment,
                        format_code!("cannot assign to constant {}", target_expr.display(ctx))
                            .as_str(),
                        loc,
                    )
                    .with_help(
                        format_code!(
                            "Consider declaring {} as a mutable local variable.",
                            &symbol.name
                        )
                        .as_str(),
                    ),
                );

                return false;
            } else if !var.is_mut {
                ctx.insert_err(
                    AnalyzeError::new(
                        ErrorKind::ImmutableAssignment,
                        format_code!(
                            "cannot assign to immutable variable {}",
                            target_expr.display(ctx)
                        )
                        .as_str(),
                        loc,
                    )
                    .with_help(
                        format_code!("Consider declaring {} as mutable.", &symbol.name).as_str(),
                    ),
                );

                return false;
            }

            true
        }

        // We're assigning to a value via a pointer. Make sure the pointer is `*mut`.
        AExprKind::UnaryOperation(Operator::Defererence, operand) => {
            if let AType::Pointer(pointer_type) = ctx.get_type(operand.type_key) {
                if !pointer_type.is_mut {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::ImmutableAssignment,
                        "cannot assign via pointer to immutable data",
                        loc,
                    ).with_detail(
                        format_code!(
                            "Cannot assign via a pointer of type {} that points to an immutable value.",
                            pointer_type.display(ctx),
                        ).as_str()
                    ).with_help(
                        format_code!(
                            "For this assignment to work, {} would need to have type {}.",
                            operand.display(ctx),
                            format!("*mut {}", ctx.display_type(pointer_type.pointee_type_key)),
                        ).as_str()
                    ));

                    return false;
                }
            }

            true
        }

        // We're assigning to a field on a struct or tuple. Make sure the base variable is mutable.
        AExprKind::MemberAccess(access) => check_assignable(ctx, loc, &access.base_expr),

        // We're assigning to a slot in an array. Make sure the array is mutable.
        AExprKind::Index(index) => check_assignable(ctx, loc, &index.collection_expr),

        // Cannot assign to other types of expressions because they're not variables.
        other => {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::InvalidAssignmentTarget,
                format_code!("cannot assign to non-variable {}", other.display(ctx)).as_str(),
                loc,
            ));

            false
        }
    }
}
