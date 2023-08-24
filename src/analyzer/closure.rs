use std::fmt;
use std::fmt::Formatter;

use colored::*;

use crate::analyzer::cond::RichCond;
use crate::analyzer::error::AnalyzeResult;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::{RichArg, RichRet};
use crate::analyzer::prog_context::{ProgramContext, Scope, ScopeKind};
use crate::analyzer::r#type::{RichType, TypeId};
use crate::analyzer::statement::RichStatement;
use crate::analyzer::warn::{AnalyzeWarning, WarnKind};
use crate::parser::arg::Argument;
use crate::parser::closure::Closure;
use crate::parser::cont::Continue;
use crate::parser::r#break::Break;
use crate::parser::r#type::Type;
use crate::{format_code, util};

/// Represents a semantically valid and type-rich closure.
#[derive(Debug, Clone)]
pub struct RichClosure {
    pub statements: Vec<RichStatement>,
    pub ret_type_id: Option<TypeId>,
    pub original: Closure,
}

impl fmt::Display for RichClosure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{...}}")
    }
}

impl PartialEq for RichClosure {
    fn eq(&self, other: &Self) -> bool {
        util::vectors_are_equal(&self.statements, &other.statements)
            && util::optionals_are_equal(&self.ret_type_id, &other.ret_type_id)
    }
}

impl RichClosure {
    /// Performs semantic analysis on the given closure and returns a type-rich version of it.
    pub fn from(
        ctx: &mut ProgramContext,
        closure: Closure,
        kind: ScopeKind,
        args: Vec<Argument>,
        expected_ret_type: Option<Type>,
    ) -> Self {
        let mut rich_args = vec![];
        for arg in args {
            rich_args.push(RichArg::from(ctx, &arg));
        }

        // Add a new scope to the program context, since each closure gets its own scope.
        let scope = Scope::new(
            kind.clone(),
            rich_args,
            match &expected_ret_type {
                Some(typ) => Some(RichType::analyze(ctx, &typ)),
                None => None,
            },
        );
        ctx.push_scope(scope);

        // Analyze all the statements in the closure and record return type.
        let original = closure.clone();
        let mut rich_statements = vec![];
        let num_statements = closure.statements.len();
        for (i, statement) in closure.statements.into_iter().enumerate() {
            let rich_statement = RichStatement::from(ctx, statement.clone());
            rich_statements.push(rich_statement);

            // If the statement is a return, make sure the return type is correct and that there
            // are no more statements in this closure.
            if let RichStatement::Return(ret) = rich_statements.last().unwrap() {
                let result = check_return(ctx, &ret, ctx.return_type().as_ref());
                ctx.consume_error(result);
                if i + 1 != num_statements {
                    ctx.add_warn(AnalyzeWarning::new_from_locatable(
                        WarnKind::UnreachableCode,
                        "statements following unconditional return would never be executed",
                        Box::new(statement.clone()),
                    ));
                    break;
                }
            }
        }

        // TODO: handle closure result.

        // Analyze the return type.
        let ret_type = match &expected_ret_type {
            Some(typ) => Some(RichType::analyze(ctx, &typ)),
            None => None,
        };

        // Pop the scope from the stack before returning since we're exiting the closure scope.
        ctx.pop_scope();
        RichClosure {
            statements: rich_statements,
            ret_type_id: ret_type,
            original,
        }
    }
}

/// Checks that the given closure returns the given type.
pub fn check_closure_returns(
    ctx: &mut ProgramContext,
    closure: &RichClosure,
    expected_ret_type_id: &TypeId,
    kind: &ScopeKind,
) {
    // Given that there is an expected return type, one of the following return conditions must
    // be satisfied by the final statement in the closure.
    //  1. It is a return statement returning a value of the right type.
    //  2. It is an exhaustive conditional where each branch closure satisfies these return
    //     conditions.
    //  3. It is a loop that contains a return anywhere that satisfies these return conditions
    //     and has no breaks.
    //  4. It is an inline closure with a final statement that that satisfies these return
    //     conditions.
    match kind {
        // If this closure is a function body, branch body, or inline closure, we need to ensure
        // that the final statement satisfies the return conditions.
        ScopeKind::FnBody | ScopeKind::Branch | ScopeKind::Inline => {
            match closure.statements.last() {
                // If it's a return, make sure the return type is correct.
                Some(RichStatement::Return(ret)) => {
                    let result = check_return(ctx, &ret, Some(expected_ret_type_id));
                    ctx.consume_error(result);
                }

                // If it's a conditional, make sure it is exhaustive and recurse on each branch.
                Some(RichStatement::Conditional(cond)) => {
                    check_cond_returns(ctx, &cond, expected_ret_type_id);
                }

                // If it's a loop, recurse on the loop body.
                Some(RichStatement::Loop(closure)) => {
                    check_closure_returns(ctx, &closure, expected_ret_type_id, &ScopeKind::Loop);
                }

                // If it's an inline closure, recurse on the closure.
                Some(RichStatement::Closure(closure)) => {
                    check_closure_returns(ctx, &closure, expected_ret_type_id, &ScopeKind::Inline);
                }

                _ => {
                    ctx.add_err(AnalyzeError::new_with_locatable(
                        ErrorKind::MissingReturn,
                        "missing return statement",
                        Box::new(closure.original.clone()),
                    ));
                }
            };
        }

        // If this closure is a loop, we need to check that it contains a return anywhere
        // that satisfies the return conditions, and that it has no breaks.
        ScopeKind::Loop => {
            let mut contains_return = false;
            for statement in &closure.statements {
                match statement {
                    RichStatement::Break => {
                        ctx.add_err(
                            AnalyzeError::new_with_locatable(
                                ErrorKind::MissingReturn,
                                "missing return statement",
                                Box::new(closure.original.clone()),
                            )
                            .with_detail(
                                "final statement is a loop that contains break statements",
                            ),
                        );
                    }
                    RichStatement::Return(ret) => {
                        let result = check_return(ctx, ret, Some(expected_ret_type_id));
                        ctx.consume_error(result);
                        contains_return = true;
                    }
                    RichStatement::Conditional(cond) => {
                        if cond_has_any_return(cond) {
                            contains_return = true;
                        }
                    }
                    RichStatement::Loop(closure) => {
                        if closure_has_any_return(closure) {
                            contains_return = true;
                        }
                    }
                    RichStatement::Closure(closure) => {
                        if closure_has_any_return(closure) {
                            contains_return = true;
                        }
                    }
                    _ => {}
                }
            }

            if !contains_return {
                ctx.add_err(
                    AnalyzeError::new_with_locatable(
                        ErrorKind::MissingReturn,
                        "missing return statement",
                        Box::new(closure.original.clone()),
                    )
                    .with_detail("final statement is a loop that does not return"),
                );
            }
        }
    };
}

/// Returns true if the closure contains a return at any level.
fn closure_has_any_return(closure: &RichClosure) -> bool {
    for statement in &closure.statements {
        match statement {
            RichStatement::Return(_) => {
                return true;
            }
            RichStatement::Conditional(cond) => {
                if cond_has_any_return(cond) {
                    return true;
                }
            }
            RichStatement::Loop(closure) => {
                if closure_has_any_return(closure) {
                    return true;
                }
            }
            RichStatement::Closure(closure) => {
                if closure_has_any_return(closure) {
                    return true;
                }
            }
            _ => {}
        };
    }

    false
}

/// Returns true if the conditional contains a return at any level.
fn cond_has_any_return(cond: &RichCond) -> bool {
    for branch in &cond.branches {
        if closure_has_any_return(&branch.body) {
            return true;
        }
    }

    false
}

/// Checks that the given conditional is exhaustive and that each branch satisfies return
/// conditions.
fn check_cond_returns(ctx: &mut ProgramContext, cond: &RichCond, expected: &TypeId) {
    if !cond.is_exhaustive() {
        ctx.add_err(
            AnalyzeError::new_with_locatable(
                ErrorKind::MissingReturn,
                "missing return statement",
                Box::new(cond.clone()),
            )
            .with_detail("final statement is a conditional that is not exhaustive"),
        );
        return;
    }

    for branch in &cond.branches {
        check_closure_returns(ctx, &branch.body, expected, &ScopeKind::Branch);
    }
}

/// Checks that the return type matches what is expected.
fn check_return(
    ctx: &ProgramContext,
    ret: &RichRet,
    expected: Option<&TypeId>,
) -> AnalyzeResult<()> {
    match expected {
        Some(expected_type_id) => match &ret.val {
            Some(expr) => {
                let expected_type = ctx.get_resolved_type(expected_type_id).unwrap();
                let expr_type = ctx.get_resolved_type(&expr.type_id).unwrap();

                // Skip the type check if either type is unknown. This will happen if semantic
                // analysis on either type already failed.
                if !expr_type.is_unknown()
                    && !expected_type.is_unknown()
                    && &expr.type_id != expected_type_id
                {
                    return Err(AnalyzeError::new_with_locatable(
                        ErrorKind::IncompatibleTypes,
                        format_code!(
                            "expected return value of type {}, but found {}",
                            expected_type,
                            expr_type,
                        )
                        .as_str(),
                        Box::new(ret.clone()),
                    ));
                }
            }
            None => {
                return Err(AnalyzeError::new_with_locatable(
                    ErrorKind::MissingReturn,
                    format_code!(
                        "return statement is missing a required value of type {}",
                        expected_type_id,
                    )
                    .as_str(),
                    Box::new(ret.clone()),
                ))
            }
        },
        None => {
            // There is no expected return type, so make sure we're returning nothing.
            if ret.val.is_some() {
                return Err(AnalyzeError::new_with_locatable(
                    ErrorKind::IncompatibleTypes,
                    "cannot return value from function with no return type",
                    Box::new(ret.clone()),
                ));
            }
        }
    }

    Ok(())
}

/// Performs semantic analysis on a break statement.
pub fn analyze_break(ctx: &mut ProgramContext, br: &Break) {
    // Make sure we are inside a loop closure.
    if !ctx.is_in_loop() {
        ctx.add_err(AnalyzeError::new_with_locatable(
            ErrorKind::UnexpectedBreak,
            "cannot break from outside a loop",
            Box::new(br.clone()),
        ));
    }
}

/// Performs semantic analysis on a continue statement.
pub fn analyze_continue(ctx: &mut ProgramContext, cont: &Continue) {
    // Make sure we are inside a loop closure.
    if !ctx.is_in_loop() {
        ctx.add_err(AnalyzeError::new_with_locatable(
            ErrorKind::UnexpectedContinue,
            "cannot continue from outside a loop",
            Box::new(cont.clone()),
        ));
    }
}
