use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::ast::arg::AArg;
use crate::analyzer::ast::cond::ACond;
use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::r#match::{AMatch, APattern};
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::error::{
    err_dup_fn_arg, err_missing_return, err_missing_yield, err_unexpected_break,
    err_unexpected_continue,
};
use crate::analyzer::ident::Ident;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::{Scope, ScopeKind};
use crate::analyzer::type_store::TypeKey;
use crate::analyzer::warn::warn_unreachable;
use crate::lexer::pos::Span;
use crate::locatable_impl;
use crate::parser::ast::arg::Argument;
use crate::parser::ast::closure::Closure;
use crate::parser::ast::cont::Continue;
use crate::parser::ast::r#break::Break;
use crate::parser::ast::r#type::Type;
use crate::Locatable;

/// Represents a semantically valid and fully analyzed closure.
#[derive(Debug, Clone)]
pub struct AClosure {
    pub statements: Vec<AStatement>,
    pub ret_type_key: Option<TypeKey>,
    pub span: Span,
}

locatable_impl!(AClosure);

impl fmt::Display for AClosure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{...}}")
    }
}

impl PartialEq for AClosure {
    fn eq(&self, other: &Self) -> bool {
        self.statements == other.statements && self.ret_type_key == other.ret_type_key
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

    /// Performs semantic analysis on the given closure and returns analyzed version of it.
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

        let a_expected_ret_type = expected_ret_type.as_ref().map(|typ| ctx.resolve_type(typ));

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
        let start_pos = closure.span().start_pos;
        let end_pos = closure.span().end_pos;

        // Add a new scope to the program context, since each closure gets its own scope.
        ctx.push_scope(Scope::new(kind, expected_ret_type_key));

        for arg in a_args {
            if ctx
                .insert_ident(Ident::new_var(
                    arg.name.clone(),
                    arg.is_mut,
                    arg.type_key,
                    arg.span,
                ))
                .is_err()
            {
                ctx.insert_err(err_dup_fn_arg(&arg.name, arg.span));
            }
        }

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
                AStatement::Break(_)
                    | AStatement::Continue(_)
                    | AStatement::Return(_)
                    | AStatement::Yield(_)
            );

            // If this statement jumps away from this closure but there are still more statements
            // following the jump inside this closure, issue a warning that those statements will
            // never be executed.
            let is_last = i + 1 == num_statements;
            if has_terminator && !is_last {
                ctx.insert_warn(warn_unreachable(&a_statement, *statement.span()));
                a_statements.push(a_statement);
                break;
            }

            a_statements.push(a_statement);
        }

        ctx.pop_scope(true);

        AClosure {
            statements: a_statements,
            ret_type_key: expected_ret_type_key,
            span: Span {
                file_id: closure.span().file_id,
                start_pos,
                end_pos,
            },
        }
    }
}

/// Checks that the given closure is guaranteed to return (or run forever). If
/// there is an error, it will be added to the program context.
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
        ScopeKind::FnBody
        | ScopeKind::BranchBody
        | ScopeKind::FromBody
        | ScopeKind::InlineClosure => {
            match closure.statements.last() {
                // If it's a return, we're done checking. We don't need to validate the return
                // itself because return statements are validated in `ARet::from`.
                Some(AStatement::Return(_)) => {}

                // If it's a conditional, make sure it is exhaustive and recurse on each branch.
                Some(AStatement::Conditional(cond)) => {
                    check_cond_returns(ctx, cond);
                }

                // If it's a loop, recurse on the loop body.
                Some(AStatement::Loop(loop_)) => {
                    if loop_.maybe_cond.is_some() {
                        ctx.insert_err(err_missing_return(
                            Some("The last statement in this closure is a loop that is not guaranteed to return."),
                            closure.span,
                        ));
                    }

                    check_closure_returns(ctx, &loop_.body, &ScopeKind::LoopBody);
                }

                // If it's an inline closure, recurse on the closure.
                Some(AStatement::Closure(closure)) => {
                    check_closure_returns(ctx, closure, &ScopeKind::InlineClosure);
                }

                // If it's a match statement, make sure all cases return.
                Some(AStatement::Match(match_)) => {
                    for case in &match_.cases {
                        check_closure_returns(ctx, &case.body, &ScopeKind::BranchBody);
                    }
                }

                _ => {
                    ctx.insert_err(err_missing_return(None, closure.span));
                }
            };
        }

        // If this closure is a loop, we need to check that it contains a return anywhere
        // that satisfies the return conditions, and that it has no breaks.
        ScopeKind::LoopBody => {
            if closure_has_any_break(closure) || !closure_has_any_return(closure) {
                ctx.insert_err(err_missing_return(
                    Some("The last statement in this closure is a loop that is not guaranteed to return."),
                    closure.span,
                ));
            }
        }

        other => panic!("unexpected scope kind {:?}", other),
    };
}

/// Returns true if the closure contains a return at any level.
fn closure_has_any_return(closure: &AClosure) -> bool {
    search_closure(closure, &|statement| {
        matches!(statement, AStatement::Return(_))
    })
}

/// Returns true if the closure contains a yield at any level.
fn closure_has_any_yield(closure: &AClosure) -> bool {
    search_closure(closure, &|statement| {
        matches!(statement, AStatement::Yield(_))
    })
}

/// Searches a closure recursively for a statement that causes `is_match` to
/// return `true`. Returns true if a match was found and false otherwise.
fn search_closure(closure: &AClosure, is_match: &impl Fn(&AStatement) -> bool) -> bool {
    for statement in &closure.statements {
        if search_statement(statement, is_match) {
            return true;
        }
    }

    false
}

/// Recursively searches `closure` for an expression that satisfies `is_match`.
fn search_closure_for_expr(closure: &AClosure, is_match: &impl Fn(&AExpr) -> bool) -> bool {
    for statement in &closure.statements {
        if search_statement_for_expr(statement, is_match) {
            return true;
        }
    }

    false
}

/// Recursively searches `expr` for a statement that satisfies `is_match`.
fn search_expr_for_statement(expr: &AExpr, is_match: &impl Fn(&AStatement) -> bool) -> bool {
    match &expr.kind {
        AExprKind::MemberAccess(access) => search_expr_for_statement(&access.base_expr, is_match),

        AExprKind::StructInit(struct_init) => {
            for (_, val) in &struct_init.field_values {
                if search_expr_for_statement(val, is_match) {
                    return true;
                }
            }

            false
        }

        AExprKind::EnumInit(enum_init) => enum_init
            .maybe_value
            .as_ref()
            .is_some_and(|val| search_expr_for_statement(val, is_match)),

        AExprKind::TupleInit(tuple_init) => {
            for value in &tuple_init.values {
                if search_expr_for_statement(value, is_match) {
                    return true;
                }
            }

            false
        }

        AExprKind::ArrayInit(array_init) => {
            for value in &array_init.values {
                if search_expr_for_statement(value, is_match) {
                    return true;
                }
            }

            false
        }

        AExprKind::Index(index) => {
            search_expr_for_statement(&index.index_expr, is_match)
                || search_expr_for_statement(&index.collection_expr, is_match)
        }

        AExprKind::FunctionCall(call) => {
            for arg in &call.args {
                if search_expr_for_statement(arg, is_match) {
                    return true;
                }
            }

            false
        }

        AExprKind::UnaryOperation(_, operand) => search_expr_for_statement(operand, is_match),

        AExprKind::BinaryOperation(left, _, right) => {
            search_expr_for_statement(left, is_match) || search_expr_for_statement(right, is_match)
        }

        AExprKind::TypeCast(val, _) => search_expr_for_statement(val, is_match),

        AExprKind::From(statement) => search_statement(statement, is_match),

        // These expressions can't contain statements.
        AExprKind::Symbol(_)
        | AExprKind::BoolLiteral(_)
        | AExprKind::I8Literal(_)
        | AExprKind::U8Literal(_)
        | AExprKind::I16Literal(_)
        | AExprKind::U16Literal(_)
        | AExprKind::I32Literal(_)
        | AExprKind::U32Literal(_)
        | AExprKind::F32Literal(_)
        | AExprKind::I64Literal(_)
        | AExprKind::U64Literal(_)
        | AExprKind::F64Literal(_, _)
        | AExprKind::IntLiteral(_, _)
        | AExprKind::UintLiteral(_)
        | AExprKind::StrLiteral(_)
        | AExprKind::CharLiteral(_)
        | AExprKind::AnonFunction(_)
        | AExprKind::Sizeof(_)
        | AExprKind::Unknown => false,
    }
}

/// Recursively searches `expr` for an expression that satisfies `is_match`.
fn search_expr(expr: &AExpr, is_match: &impl Fn(&AExpr) -> bool) -> bool {
    if is_match(expr) {
        return true;
    }

    match &expr.kind {
        AExprKind::MemberAccess(access) => search_expr(&access.base_expr, is_match),

        AExprKind::StructInit(struct_init) => {
            for (_, value) in &struct_init.field_values {
                if search_expr(value, is_match) {
                    return true;
                }
            }

            false
        }

        AExprKind::EnumInit(enum_init) => enum_init
            .maybe_value
            .as_ref()
            .is_some_and(|val| search_expr(val, is_match)),

        AExprKind::TupleInit(tuple_init) => {
            for value in &tuple_init.values {
                if search_expr(value, is_match) {
                    return true;
                }
            }

            false
        }

        AExprKind::ArrayInit(array_init) => {
            for value in &array_init.values {
                if search_expr(value, is_match) {
                    return true;
                }
            }

            false
        }

        AExprKind::Index(index) => {
            search_expr(&index.index_expr, is_match)
                || search_expr(&index.collection_expr, is_match)
        }

        AExprKind::FunctionCall(call) => {
            if search_expr(&call.fn_expr, is_match) {
                return true;
            }

            for arg in &call.args {
                if search_expr(arg, is_match) {
                    return true;
                }
            }

            false
        }

        AExprKind::UnaryOperation(_, operand) => search_expr(operand, is_match),

        AExprKind::BinaryOperation(left, _, right) => {
            search_expr(left, is_match) || search_expr(right, is_match)
        }

        AExprKind::TypeCast(expr, _) => search_expr(expr, is_match),

        AExprKind::From(statement) => search_statement_for_expr(statement, is_match),

        // These expressions don't contain other expressions.
        AExprKind::Sizeof(_)
        | AExprKind::Symbol(_)
        | AExprKind::BoolLiteral(_)
        | AExprKind::I8Literal(_)
        | AExprKind::U8Literal(_)
        | AExprKind::I16Literal(_)
        | AExprKind::U16Literal(_)
        | AExprKind::I32Literal(_)
        | AExprKind::U32Literal(_)
        | AExprKind::F32Literal(_)
        | AExprKind::I64Literal(_)
        | AExprKind::U64Literal(_)
        | AExprKind::F64Literal(_, _)
        | AExprKind::IntLiteral(_, _)
        | AExprKind::UintLiteral(_)
        | AExprKind::StrLiteral(_)
        | AExprKind::CharLiteral(_)
        | AExprKind::AnonFunction(_)
        | AExprKind::Unknown => false,
    }
}

/// Recursively searches `statement` for a statement that satisfies `is_match`.
fn search_statement(statement: &AStatement, is_match: &impl Fn(&AStatement) -> bool) -> bool {
    if is_match(statement) {
        return true;
    }

    match statement {
        AStatement::Closure(closure) => search_closure(closure, is_match),

        AStatement::Conditional(cond) => {
            for branch in &cond.branches {
                if let Some(cond) = &branch.cond {
                    if search_expr(cond, &|expr| search_expr_for_statement(expr, is_match)) {
                        return true;
                    }
                }

                if search_closure(&branch.body, is_match) {
                    return true;
                }
            }

            false
        }

        AStatement::Match(match_) => {
            for case in &match_.cases {
                match &case.pattern {
                    APattern::Exprs(patterns) => {
                        for pattern in patterns {
                            if search_expr(pattern, &|expr| {
                                search_expr_for_statement(expr, is_match)
                            }) {
                                return true;
                            }
                        }
                    }

                    APattern::LetEnumVariants(_, _, _, _)
                    | APattern::LetSymbol(_, _)
                    | APattern::Wildcard => {}
                }

                if let Some(cond) = &case.maybe_cond {
                    if search_expr(cond, &|expr| search_expr_for_statement(expr, is_match)) {
                        return true;
                    }
                }

                if search_closure(&case.body, is_match) {
                    return true;
                }
            }

            false
        }

        AStatement::Loop(loop_) => {
            if let Some(init) = &loop_.maybe_init {
                if is_match(init) {
                    return true;
                }
            }

            if let Some(cond) = &loop_.maybe_cond {
                if search_expr_for_statement(cond, is_match) {
                    return true;
                }
            }

            if search_closure(&loop_.body, is_match) {
                return true;
            }

            if let Some(update) = &loop_.maybe_update {
                if search_statement(update, is_match) {
                    return true;
                }
            }

            false
        }

        AStatement::VariableDeclaration(var_decl) => {
            search_expr_for_statement(&var_decl.val, is_match)
        }

        AStatement::VariableAssignment(assign) => {
            search_expr_for_statement(&assign.target, is_match)
                || search_expr_for_statement(&assign.val, is_match)
        }

        AStatement::FunctionCall(call) => {
            if search_expr_for_statement(&call.fn_expr, is_match) {
                return true;
            }

            for arg in &call.args {
                if search_expr_for_statement(arg, is_match) {
                    return true;
                }
            }

            false
        }

        AStatement::Return(ret) => ret
            .val
            .as_ref()
            .is_some_and(|val| search_expr_for_statement(val, is_match)),

        AStatement::Yield(yld) => search_expr_for_statement(&yld.value, is_match),

        // These statements don't contain other statements.
        AStatement::Continue(_)
        | AStatement::Break(_)
        | AStatement::FunctionDeclaration(_)
        | AStatement::StructTypeDeclaration(_)
        | AStatement::EnumTypeDeclaration(_)
        | AStatement::Const(_)
        | AStatement::Static(_) => false,
    }
}

/// Recursively searches `statement` for an expression that satisfies `is_match`.
fn search_statement_for_expr(statement: &AStatement, is_match: &impl Fn(&AExpr) -> bool) -> bool {
    match statement {
        AStatement::VariableDeclaration(var_decl) => search_expr(&var_decl.val, is_match),

        AStatement::VariableAssignment(assign) => {
            search_expr(&assign.target, is_match) || search_expr(&assign.val, is_match)
        }

        AStatement::Closure(closure) => search_closure_for_expr(closure, is_match),

        AStatement::FunctionCall(call) => {
            if search_expr(&call.fn_expr, is_match) {
                return true;
            }

            for arg in &call.args {
                if search_expr(arg, is_match) {
                    return true;
                }
            }

            false
        }

        AStatement::Conditional(cond) => {
            for branch in &cond.branches {
                if let Some(expr) = &branch.cond {
                    if search_expr(expr, is_match) {
                        return true;
                    }
                }

                if search_closure_for_expr(&branch.body, is_match) {
                    return true;
                }
            }

            false
        }

        AStatement::Match(match_) => {
            for case in &match_.cases {
                match &case.pattern {
                    APattern::Exprs(exprs) => {
                        for expr in exprs {
                            if search_expr(expr, is_match) {
                                return true;
                            }
                        }
                    }
                    APattern::Wildcard
                    | APattern::LetEnumVariants(_, _, _, _)
                    | APattern::LetSymbol(_, _) => {}
                }

                if let Some(cond) = &case.maybe_cond {
                    if search_expr(cond, is_match) {
                        return true;
                    }
                }

                if search_closure_for_expr(&case.body, is_match) {
                    return true;
                }
            }

            false
        }

        AStatement::Loop(loop_) => {
            if let Some(init) = &loop_.maybe_init {
                if search_statement_for_expr(init, is_match) {
                    return true;
                }
            }

            if let Some(cond) = &loop_.maybe_cond {
                if search_expr(cond, is_match) {
                    return true;
                }
            }

            if let Some(update) = &loop_.maybe_update {
                if search_statement_for_expr(update, is_match) {
                    return true;
                }
            }

            search_closure_for_expr(&loop_.body, is_match)
        }

        AStatement::Return(ret) => ret
            .val
            .as_ref()
            .is_some_and(|val| search_expr(val, is_match)),

        AStatement::Yield(yld) => search_expr(&yld.value, is_match),

        AStatement::Break(_)
        | AStatement::Continue(_)
        | AStatement::FunctionDeclaration(_)
        | AStatement::StructTypeDeclaration(_)
        | AStatement::EnumTypeDeclaration(_)
        | AStatement::Const(_)
        | AStatement::Static(_) => false,
    }
}

/// Returns true if the closure contains a break at any level.
fn closure_has_any_break(closure: &AClosure) -> bool {
    search_closure(closure, &|statement| match statement {
        AStatement::Break(_) => true,
        // Loops with conditions implicitly contain break statements because
        // the loop will be broken if the condition is ever false.
        AStatement::Loop(loop_) => loop_.maybe_cond.is_some(),
        _ => false,
    })
}

/// Checks that the given closure yields. If there is an error, it will be added
/// to the program context.
pub fn check_closure_yields(ctx: &mut ProgramContext, closure: &AClosure, kind: &ScopeKind) {
    // One of the following yield conditions must be satisfied by the final
    // statement in the closure.
    //  1. It is a yield statement.
    //  2. It is an exhaustive conditional/match where each branch closure satisfies these yield
    //     conditions.
    //  3. It is a loop that contains a yield anywhere that satisfies these yield conditions
    //     and has no breaks.
    //  4. It is an inline closure with a final statement that that satisfies these yield
    //     conditions.
    match kind {
        // If this closure is a function body, branch body, or inline closure, we need to ensure
        // that the final statement satisfies the yield conditions.
        ScopeKind::FnBody
        | ScopeKind::BranchBody
        | ScopeKind::FromBody
        | ScopeKind::InlineClosure => {
            match closure.statements.last() {
                // If it's a yield, we're done checking. We don't need to validate the yield
                // itself because yield statements are validated in `AYield::from`.
                Some(AStatement::Yield(_)) => {}

                // If it's a conditional, make sure it is exhaustive and recurse on each branch.
                Some(AStatement::Conditional(cond)) => {
                    check_cond_yields(ctx, cond);
                }

                Some(AStatement::Match(match_)) => {
                    check_match_yields(ctx, match_);
                }

                // If it's a loop, recurse on the loop body.
                Some(AStatement::Loop(loop_)) => {
                    if loop_.maybe_cond.is_some() {
                        ctx.insert_err(err_missing_yield(
                            Some("The last statement in this closure is a loop that is not guaranteed to yield."),
                            closure.span
                        ));
                    }

                    check_closure_yields(ctx, &loop_.body, &ScopeKind::LoopBody);
                }

                // If it's an inline closure, recurse on the closure.
                Some(AStatement::Closure(closure)) => {
                    check_closure_yields(ctx, closure, &ScopeKind::InlineClosure);
                }

                _ => {
                    ctx.insert_err(err_missing_yield(None, closure.span));
                }
            };
        }

        // If this closure is a loop, we need to check that it contains a yield anywhere
        // that satisfies the yield conditions, and that it has no breaks.
        ScopeKind::LoopBody => {
            if closure_has_any_break(closure) || !closure_has_any_yield(closure) {
                ctx.insert_err(err_missing_yield(
                    Some("The last statement in this closure is a loop that is not guaranteed to yield."),
                    closure.span
                ));
            }
        }

        other => panic!("unexpected scope kind {:?}", other),
    };
}

/// Checks that the given conditional is exhaustive and that each branch satisfies return
/// conditions.
fn check_cond_returns(ctx: &mut ProgramContext, cond: &ACond) {
    if !cond.is_exhaustive() {
        ctx.insert_err(err_missing_return(
            Some("The last statement in this closure is a conditional that is not exhaustive."),
            cond.span,
        ));
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
        ctx.insert_err(err_missing_yield(
            Some("The last statement in this closure is a conditional that is not exhaustive"),
            cond.span,
        ));
        return;
    }

    for branch in &cond.branches {
        check_closure_yields(ctx, &branch.body, &ScopeKind::BranchBody);
    }
}

/// Checks that all cases in the given match statement yield.
fn check_match_yields(ctx: &mut ProgramContext, match_: &AMatch) {
    for case in &match_.cases {
        check_closure_yields(ctx, &case.body, &ScopeKind::BranchBody)
    }
}

/// Performs semantic analysis on a break statement.
pub fn analyze_break(ctx: &mut ProgramContext, br: &Break) {
    // Make sure we are inside a loop closure.
    if !ctx.is_in_loop() {
        ctx.insert_err(err_unexpected_break(br.span));
    }
}

/// Performs semantic analysis on a continue statement.
pub fn analyze_continue(ctx: &mut ProgramContext, cont: &Continue) {
    // Make sure we are inside a loop closure.
    if !ctx.is_in_loop() {
        ctx.insert_err(err_unexpected_continue(cont.span));
    }
}
