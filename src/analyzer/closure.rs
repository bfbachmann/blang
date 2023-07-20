use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::cond::RichCond;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::RichRet;
use crate::analyzer::prog_context::{ProgramContext, Scope, ScopeKind};
use crate::analyzer::statement::RichStatement;
use crate::analyzer::AnalyzeResult;
use crate::parser::arg::Argument;
use crate::parser::closure::Closure;
use crate::parser::r#type::Type;
use crate::util;

/// Represents a semantically valid and type-rich closure.
#[derive(Debug)]
pub struct RichClosure {
    pub statements: Vec<RichStatement>,
    pub ret_type: Option<Type>,
}

impl fmt::Display for RichClosure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{...}}")
    }
}

impl PartialEq for RichClosure {
    fn eq(&self, other: &Self) -> bool {
        util::vectors_are_equal(&self.statements, &other.statements)
            && util::optionals_are_equal(&self.ret_type, &other.ret_type)
    }
}

impl RichClosure {
    /// Performs semantic analysis on the given closure and returns a type-rich version of it,
    /// or an error if the closure is semantically invalid.
    pub fn from(
        ctx: &mut ProgramContext,
        closure: Closure,
        kind: ScopeKind,
        args: Vec<Argument>,
        expected_ret_type: Option<Type>,
    ) -> AnalyzeResult<Self> {
        // Add a new scope to the program context, since each closure gets its own scope.
        ctx.push_scope(Scope::new(kind.clone(), args, expected_ret_type.clone()));

        // Analyze all the statements in the closure and record return type.
        let mut rich_statements = vec![];
        let num_statements = closure.statements.len();
        for (i, statement) in closure.statements.into_iter().enumerate() {
            let rich_statement = RichStatement::from(ctx, statement)?;

            // If the statement is a return, make sure the return type is correct and that there
            // are no more statements in this closure.
            if let RichStatement::Return(ret) = &rich_statement {
                check_return(&ret, ctx.return_type().as_ref())?;
                if i + 1 != num_statements {
                    return Err(AnalyzeError::new(
                        ErrorKind::UnexpectedReturn,
                        "statements following unconditional return would never be executed",
                    ));
                }
            }

            rich_statements.push(rich_statement);
        }

        // TODO: handle closure result.

        // Pop the scope from the stack before returning since we're exiting the closure scope.
        ctx.pop_scope();
        Ok(RichClosure {
            statements: rich_statements,
            ret_type: expected_ret_type.clone(),
        })
    }
}

/// Checks that the given closure returns the given type.
pub fn check_closure_returns(
    closure: &RichClosure,
    expected_ret_type: &Type,
    kind: &ScopeKind,
) -> AnalyzeResult<()> {
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
            let last_statement = match closure.statements.last() {
                Some(statement) => statement,
                None => {
                    return Err(AnalyzeError::new(
                        ErrorKind::MissingReturn,
                        format!("expected return value of type {}", expected_ret_type).as_str(),
                    ))
                }
            };

            match last_statement {
                // If it's a return, make sure the return type is correct.
                RichStatement::Return(ret) => check_return(ret, Some(expected_ret_type))?,

                // If it's a conditional, make sure it is exhaustive and recurse on each branch.
                RichStatement::Conditional(cond) => {
                    check_cond_returns(cond, expected_ret_type)?;
                }

                // If it's a loop, recurse on the loop body.
                RichStatement::Loop(closure) => {
                    check_closure_returns(closure, expected_ret_type, &ScopeKind::Loop)?;
                }

                // If it's an inline closure, recurse on the closure.
                RichStatement::Closure(closure) => {
                    check_closure_returns(closure, expected_ret_type, &ScopeKind::Inline)?;
                }

                _ => {
                    return Err(AnalyzeError::new(
                        ErrorKind::MissingReturn,
                        format!("expected return value of type {}", expected_ret_type).as_str(),
                    ));
                }
            }
        }

        // If this closure is a loop, we need to check that it contains a return anywhere
        // that satisfies the return conditions, and that it has no breaks.
        ScopeKind::Loop => {
            let mut contains_return = false;
            for statement in &closure.statements {
                match statement {
                    RichStatement::Break => {
                        return Err(AnalyzeError::new(
                            ErrorKind::MissingReturn,
                            format!(
                                "missing return value of type {} (final statement is \
                                    a loop that contains break statements)",
                                expected_ret_type
                            )
                            .as_str(),
                        ));
                    }
                    RichStatement::Return(ret) => {
                        check_return(ret, Some(expected_ret_type))?;
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
                return Err(AnalyzeError::new(
                    ErrorKind::MissingReturn,
                    format!(
                        "missing return value of type {} (final statement is \
                            a loop that does not return)",
                        expected_ret_type
                    )
                    .as_str(),
                ));
            }
        }
    }

    Ok(())
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
fn check_cond_returns(cond: &RichCond, expected: &Type) -> AnalyzeResult<()> {
    if !cond.is_exhaustive() {
        return Err(AnalyzeError::new(
            ErrorKind::MissingReturn,
            format!(
                "missing return value of type {} (final statement is \
                a conditional that is not exhaustive))",
                expected
            )
            .as_str(),
        ));
    }

    for branch in &cond.branches {
        check_closure_returns(&branch.body, expected, &ScopeKind::Branch)?;
    }
    Ok(())
}

/// Checks that the return type matches what is expected.
fn check_return(ret: &RichRet, expected: Option<&Type>) -> AnalyzeResult<()> {
    match expected {
        Some(expected_type) => match &ret.val {
            Some(expr) => {
                if &expr.typ != expected_type {
                    return Err(AnalyzeError::new(
                        ErrorKind::IncompatibleTypes,
                        format!(
                            "expected return value of type {}, but found {}",
                            expected_type, &expr.typ
                        )
                        .as_str(),
                    ));
                }
            }
            None => {
                return Err(AnalyzeError::new(
                    ErrorKind::MissingReturn,
                    format!("missing return value of type {}", expected_type).as_str(),
                ));
            }
        },
        None => {
            // There is no expected return type, so make sure we're returning nothing.
            if ret.val.is_some() {
                return Err(AnalyzeError::new(
                    ErrorKind::IncompatibleTypes,
                    "cannot return value from function with no return type",
                ));
            }
        }
    }

    Ok(())
}

pub fn analyze_break(ctx: &mut ProgramContext) -> AnalyzeResult<()> {
    // Make sure we are inside a loop closure.
    if ctx.is_in_loop() {
        return Ok(());
    }

    Err(AnalyzeError::new(
        ErrorKind::UnexpectedBreak,
        "cannot break from outside a loop",
    ))
}
