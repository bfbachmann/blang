use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::ast::arg::AArg;
use crate::analyzer::ast::cond::ACond;
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::{Scope, ScopeKind};
use crate::analyzer::type_store::TypeKey;
use crate::analyzer::warn::{AnalyzeWarning, WarnKind};
use crate::lexer::pos::{Locatable, Position, Span};
use crate::parser::ast::arg::Argument;
use crate::parser::ast::closure::Closure;
use crate::parser::ast::cont::Continue;
use crate::parser::ast::r#break::Break;
use crate::parser::ast::r#type::Type;
use crate::{format_code, locatable_impl, util};

/// Represents a semantically valid and fully analyzed closure.
#[derive(Debug, Clone)]
pub struct AClosure {
    pub statements: Vec<AStatement>,
    pub ret_type_key: Option<TypeKey>,
    span: Span,
}

locatable_impl!(AClosure);

impl fmt::Display for AClosure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{...}}")
    }
}

impl PartialEq for AClosure {
    fn eq(&self, other: &Self) -> bool {
        util::vecs_eq(&self.statements, &other.statements)
            && util::opts_eq(&self.ret_type_key, &other.ret_type_key)
    }
}

impl AClosure {
    /// Creates a new empty closure.
    pub fn new_empty() -> Self {
        AClosure {
            statements: vec![],
            ret_type_key: None,
            span: Default::default(),
        }
    }

    /// Creates a new closure with the given statements and span.
    pub fn new(statements: Vec<AStatement>, span: Span) -> AClosure {
        AClosure {
            statements,
            ret_type_key: None,
            span,
        }
    }

    /// Performs semantic analysis on the given closure and returns a type-a version of it.
    pub fn from(
        ctx: &mut ProgramContext,
        closure: &Closure,
        kind: ScopeKind,
        args: Vec<Argument>,
        expected_ret_type: Option<Type>,
    ) -> Self {
        let mut a_args = vec![];
        for arg in args {
            a_args.push(AArg::from(ctx, &arg));
        }

        let a_expected_ret_type = match &expected_ret_type {
            Some(typ) => Some(ctx.resolve_type(&typ)),
            None => None,
        };

        AClosure::from_analyzed(ctx, closure, kind, a_args, a_expected_ret_type)
    }

    /// Performs semantic analysis on the given closure with the already-analyzed arguments and
    /// expected return type key.
    pub fn from_analyzed(
        ctx: &mut ProgramContext,
        closure: &Closure,
        kind: ScopeKind,
        a_args: Vec<AArg>,
        expected_ret_type_key: Option<TypeKey>,
    ) -> Self {
        let start_pos = closure.start_pos().clone();
        let end_pos = closure.end_pos().clone();

        // Add a new scope to the program context, since each closure gets its own scope.
        let scope = Scope::new(kind, a_args, expected_ret_type_key);
        ctx.push_scope(scope);

        // Analyze all the statements in the closure and record return type.
        let mut a_statements = vec![];
        let num_statements = closure.statements.len();
        for (i, statement) in closure.statements.iter().enumerate() {
            // Analyze the statement.
            let a_statement = AStatement::from(ctx, statement);

            // Check if the statement is a break, continue, or return, so we can mark this closure
            // as containing such statements.
            let has_terminator = matches!(
                a_statement,
                AStatement::Break
                    | AStatement::Continue
                    | AStatement::Return(_)
                    | AStatement::Yield(_)
            );

            // If this statement jumps away from this closure but there are still more statements
            // following the jump inside this closure, issue a warning that those statements will
            // never be executed.
            let is_last = i + 1 == num_statements;
            if has_terminator && !is_last {
                ctx.insert_warn(AnalyzeWarning::new(
                    WarnKind::UnreachableCode,
                    format_code!(
                        "statements following {} will never be executed",
                        match a_statement {
                            AStatement::Continue => "continue",
                            AStatement::Break => "break",
                            AStatement::Yield(_) => "yield",
                            AStatement::Return(_) => "return",
                            _ => unreachable!(),
                        }
                    )
                    .as_str(),
                    statement,
                ));
                a_statements.push(a_statement);
                break;
            }

            a_statements.push(a_statement);
        }

        ctx.pop_scope();

        AClosure {
            statements: a_statements,
            ret_type_key: expected_ret_type_key,
            span: Span { start_pos, end_pos },
        }
    }
}

/// Checks that the given closure returns. If there is an error, it will be added
/// to the program context.
pub fn check_closure_returns(ctx: &mut ProgramContext, closure: &AClosure, kind: &ScopeKind) {
    // One of the following return conditions must be satisfied by the final
    // statement in the closure.
    //  1. It is a return statement.
    //  2. It is an exhaustive conditional where each branch closure satisfies these return
    //     conditions.
    //  3. It is a loop that contains a return anywhere that satisfies these return conditions
    //     and has no breaks.
    //  4. It is an inline closure with a final statement that that satisfies these return
    //     conditions.
    match kind {
        // If this closure is a function body, branch body, or inline closure, we need to ensure
        // that the final statement satisfies the return conditions.
        ScopeKind::FnBody(_)
        | ScopeKind::BranchBody
        | ScopeKind::FromBody
        | ScopeKind::InlineClosure => {
            match closure.statements.last() {
                // If it's a return, we're done checking. We don't need to validate the return
                // itself because return statements are validated in `ARet::from`.
                Some(AStatement::Return(_)) => {}

                // If it's a conditional, make sure it is exhaustive and recurse on each branch.
                Some(AStatement::Conditional(cond)) => {
                    check_cond_returns(ctx, &cond);
                }

                // If it's a loop, recurse on the loop body.
                Some(AStatement::Loop(loop_)) => {
                    check_closure_returns(ctx, &loop_.body, &ScopeKind::LoopBody);
                }

                // If it's an inline closure, recurse on the closure.
                Some(AStatement::Closure(closure)) => {
                    check_closure_returns(ctx, &closure, &ScopeKind::InlineClosure);
                }

                _ => {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::MissingReturn,
                        "missing return statement",
                        closure,
                    ));
                }
            };
        }

        // If this closure is a loop, we need to check that it contains a return anywhere
        // that satisfies the return conditions, and that it has no breaks.
        ScopeKind::LoopBody => {
            let mut contains_return = false;
            for statement in &closure.statements {
                match statement {
                    AStatement::Break => {
                        ctx.insert_err(
                            AnalyzeError::new(
                                ErrorKind::MissingReturn,
                                "missing return statement",
                                closure,
                            )
                            .with_detail(
                                "The last statement in this closure is a loop that contains \
                                break statements.",
                            ),
                        );
                    }
                    AStatement::Return(_) => {
                        contains_return = true;
                    }
                    AStatement::Conditional(cond) => {
                        if cond_has_any_return(cond) {
                            contains_return = true;
                        }
                    }
                    AStatement::Loop(loop_) => {
                        if closure_has_any_return(&loop_.body) {
                            contains_return = true;
                        }
                    }
                    AStatement::Closure(closure) => {
                        if closure_has_any_return(closure) {
                            contains_return = true;
                        }
                    }
                    _ => {}
                }
            }

            if !contains_return {
                ctx.insert_err(
                    AnalyzeError::new(
                        ErrorKind::MissingReturn,
                        "missing return statement",
                        closure,
                    )
                    .with_detail(
                        "The last statement in this closure is a loop that does not return.",
                    ),
                );
            }
        }
    };
}

/// Returns true if the closure contains a return at any level.
fn closure_has_any_return(closure: &AClosure) -> bool {
    for statement in &closure.statements {
        match statement {
            AStatement::Return(_) => {
                return true;
            }
            AStatement::Conditional(cond) => {
                if cond_has_any_return(cond) {
                    return true;
                }
            }
            AStatement::Loop(loop_) => {
                if closure_has_any_return(&loop_.body) {
                    return true;
                }
            }
            AStatement::Closure(closure) => {
                if closure_has_any_return(closure) {
                    return true;
                }
            }
            _ => {}
        };
    }

    false
}

/// Returns true if the closure contains a yield at any level.
fn closure_has_any_yield(closure: &AClosure) -> bool {
    for statement in &closure.statements {
        match statement {
            AStatement::Yield(_) => {
                return true;
            }
            AStatement::Conditional(cond) => {
                if cond_has_any_return(cond) {
                    return true;
                }
            }
            AStatement::Loop(loop_) => {
                if closure_has_any_yield(&loop_.body) {
                    return true;
                }
            }
            AStatement::Closure(closure) => {
                if closure_has_any_yield(closure) {
                    return true;
                }
            }
            _ => {}
        };
    }

    false
}

/// Checks that the given closure yields. If there is an error, it will be added
/// to the program context.
pub fn check_closure_yields(ctx: &mut ProgramContext, closure: &AClosure, kind: &ScopeKind) {
    // One of the following yield conditions must be satisfied by the final
    // statement in the closure.
    //  1. It is a yield statement.
    //  2. It is an exhaustive conditional where each branch closure satisfies these yield
    //     conditions.
    //  3. It is a loop that contains a yield anywhere that satisfies these yield conditions
    //     and has no breaks.
    //  4. It is an inline closure with a final statement that that satisfies these yield
    //     conditions.
    match kind {
        // If this closure is a function body, branch body, or inline closure, we need to ensure
        // that the final statement satisfies the yield conditions.
        ScopeKind::FnBody(_)
        | ScopeKind::BranchBody
        | ScopeKind::FromBody
        | ScopeKind::InlineClosure => {
            match closure.statements.last() {
                // If it's a yield, we're done checking. We don't need to validate the yield
                // itself because yield statements are validated in `AYield::from`.
                Some(AStatement::Yield(_)) => {}

                // If it's a conditional, make sure it is exhaustive and recurse on each branch.
                Some(AStatement::Conditional(cond)) => {
                    check_cond_yields(ctx, &cond);
                }

                // If it's a loop, recurse on the loop body.
                Some(AStatement::Loop(loop_)) => {
                    check_closure_yields(ctx, &loop_.body, &ScopeKind::LoopBody);
                }

                // If it's an inline closure, recurse on the closure.
                Some(AStatement::Closure(closure)) => {
                    check_closure_yields(ctx, &closure, &ScopeKind::InlineClosure);
                }

                _ => {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::MissingYield,
                        format_code!("missing {}", "yield").as_str(),
                        closure,
                    ));
                }
            };
        }

        // If this closure is a loop, we need to check that it contains a yield anywhere
        // that satisfies the yield conditions, and that it has no breaks.
        ScopeKind::LoopBody => {
            let mut contains_yield = false;
            for statement in &closure.statements {
                match statement {
                    AStatement::Break => {
                        ctx.insert_err(
                            AnalyzeError::new(
                                ErrorKind::MissingYield,
                                format_code!("missing {}", "yield").as_str(),
                                closure,
                            )
                            .with_detail(
                                "The last statement in this closure is a loop that contains \
                                break statements.",
                            ),
                        );
                    }
                    AStatement::Yield(_) => {
                        contains_yield = true;
                    }
                    AStatement::Conditional(cond) => {
                        if cond_has_any_yield(cond) {
                            contains_yield = true;
                        }
                    }
                    AStatement::Loop(loop_) => {
                        if closure_has_any_yield(&loop_.body) {
                            contains_yield = true;
                        }
                    }
                    AStatement::Closure(closure) => {
                        if closure_has_any_yield(closure) {
                            contains_yield = true;
                        }
                    }
                    _ => {}
                }
            }

            if !contains_yield {
                ctx.insert_err(
                    AnalyzeError::new(ErrorKind::MissingYield, "missing yield statement", closure)
                        .with_detail(
                            "The last statement in this closure is a loop that does not yield.",
                        ),
                );
            }
        }
    };
}

/// Returns true if the conditional contains a return at any level.
fn cond_has_any_return(cond: &ACond) -> bool {
    for branch in &cond.branches {
        if closure_has_any_return(&branch.body) {
            return true;
        }
    }

    false
}

/// Returns true if the conditional contains a yield at any level.
fn cond_has_any_yield(cond: &ACond) -> bool {
    for branch in &cond.branches {
        if closure_has_any_yield(&branch.body) {
            return true;
        }
    }

    false
}

/// Checks that the given conditional is exhaustive and that each branch satisfies return
/// conditions.
fn check_cond_returns(ctx: &mut ProgramContext, cond: &ACond) {
    if !cond.is_exhaustive() {
        ctx.insert_err(
            AnalyzeError::new(ErrorKind::MissingReturn, "missing return statement", cond)
                .with_detail(
                    "The last statement in this closure is a conditional that is not exhaustive",
                ),
        );
        return;
    }

    for branch in &cond.branches {
        check_closure_returns(ctx, &branch.body, &ScopeKind::BranchBody);
    }
}

/// Checks that the given conditional is exhaustive and that each branch satisfies yield
/// conditions.
fn check_cond_yields(ctx: &mut ProgramContext, cond: &ACond) {
    if !cond.is_exhaustive() {
        ctx.insert_err(
            AnalyzeError::new(ErrorKind::MissingYield, "missing yield statement", cond)
                .with_detail(
                    "The last statement in this closure is a conditional that is not exhaustive",
                ),
        );
        return;
    }

    for branch in &cond.branches {
        check_closure_yields(ctx, &branch.body, &ScopeKind::BranchBody);
    }
}

/// Performs semantic analysis on a break statement.
pub fn analyze_break(ctx: &mut ProgramContext, br: &Break) {
    // Make sure we are inside a loop closure.
    if !ctx.is_in_loop() {
        ctx.insert_err(AnalyzeError::new(
            ErrorKind::UnexpectedBreak,
            "cannot break from outside a loop",
            br,
        ));
    }
}

/// Performs semantic analysis on a continue statement.
pub fn analyze_continue(ctx: &mut ProgramContext, cont: &Continue) {
    // Make sure we are inside a loop closure.
    if !ctx.is_in_loop() {
        ctx.insert_err(AnalyzeError::new(
            ErrorKind::UnexpectedContinue,
            "cannot continue from outside a loop",
            cont,
        ));
    }
}
