use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::analyzer::ast::closure::AClosure;
use crate::analyzer::ast::cond::ACond;
use crate::analyzer::ast::expr::AExprKind;
use crate::analyzer::ast::fn_call::AFnCall;
use crate::analyzer::ast::func::AFn;
use crate::analyzer::ast::program::AProgram;
use crate::analyzer::ast::r#impl::AImpl;
use crate::analyzer::ast::r#struct::AStructInit;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::ret::ARet;
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::ast::symbol::ASymbol;
use crate::analyzer::ast::var_assign::AVarAssign;
use crate::analyzer::ast::var_dec::AVarDecl;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::scope::ScopeKind;
use crate::analyzer::type_store::{TypeKey, TypeStore};
use crate::lexer::pos::{Locatable, Position};
use crate::{format_code, locatable_impl};

/// Represents the change in ownership of a variable or value.
#[derive(Clone)]
struct Move {
    path: Vec<String>,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(Move);

impl Display for Move {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.path.join("."))
    }
}

impl Move {
    /// Creates a new move from `var`.
    fn from(var: &ASymbol) -> Self {
        Move {
            path: var.to_string().split(".").map(|s| s.to_string()).collect(),
            start_pos: var.start_pos().clone(),
            end_pos: var.end_pos().clone(),
        }
    }

    /// Returns the name of the root variable that was moved.
    fn var_name(&self) -> &str {
        self.path.first().unwrap().as_str()
    }

    /// Returns true if this move would conflict with `other`.
    fn conflicts_with(&self, other: &Move) -> bool {
        self.has_prefix(&other.path) || other.has_prefix(&self.path)
    }

    /// Returns true if the path represented by `prefix` is the same as or is a parent of this
    /// move's path.
    fn has_prefix(&self, prefix: &Vec<String>) -> bool {
        if self.path.len() < prefix.len() {
            return false;
        }

        for (s1, s2) in self.path.iter().zip(prefix.iter()) {
            if s1 != s2 {
                return false;
            }
        }

        true
    }
}

/// Represents a closure scope (i.e. loop body, branch body, function body or inline closure).
struct Scope {
    kind: ScopeKind,
    /// Variables that were declared directly within this scope.
    declared_vars: HashSet<String>,
    /// Variables moves that occur within this scope.
    moved_vars: HashMap<String, Vec<Move>>,
    /// Deferred moves are moves that can only conflict with moves that occur after this scope and
    /// not with moves that occur within or under this scope. The prime example is any move that
    /// occurs before a `break` inside a branch inside a loop, because it can't conflict with any
    /// moves after it in the loop, but can conflict with moves after the loop.
    deferred_moves: HashMap<String, Vec<Move>>,
    /// Will be true if the scope is guaranteed to return.
    has_return: bool,
    /// Will be true if the scope is guaranteed to break.
    has_break: bool,
}

impl Scope {
    /// Creates a new scope.
    fn new(kind: ScopeKind, has_return: bool, has_break: bool) -> Self {
        Scope {
            kind,
            declared_vars: HashSet::new(),
            moved_vars: HashMap::new(),
            deferred_moves: HashMap::new(),
            has_return,
            has_break,
        }
    }

    /// Creates a new scope representing a function body.
    fn new_fn_body() -> Self {
        Scope {
            kind: ScopeKind::FnBody,
            declared_vars: HashSet::new(),
            moved_vars: HashMap::new(),
            deferred_moves: HashMap::new(),
            has_return: true,
            has_break: false,
        }
    }

    /// Returns true if this scope is guaranteed to exit its enclosing loop (i.e. it has a `break`
    /// or `return` statement).
    fn exits_loop(&self) -> bool {
        self.has_break || self.has_return
    }

    /// Returns all moves that conflict with `mv`.
    fn get_conflicting_moves(&self, mv: &Move) -> Vec<&Move> {
        // Check all the moves that occurred for this variable in this scope.
        let var_name = mv.var_name();
        let mut conflicting_moves = vec![];
        if let Some(existing_moves) = self.moved_vars.get(var_name) {
            for existing_move in existing_moves {
                if existing_move.conflicts_with(&mv) {
                    conflicting_moves.push(existing_move);
                }
            }
        }

        conflicting_moves
    }

    /// Removes all moves of the variable with the given name from this scope.
    fn clear_moves(&mut self, var_name: &str) {
        self.moved_vars.remove(var_name);
    }

    /// Adds `mv` to this scope. If `deferred` is true, adds the move as a deferred move, so it
    /// will only be checked against other moves after this scope and none within or under this
    /// scope.
    fn add_move(&mut self, mv: Move, deferred: bool) {
        let target = match deferred {
            true => &mut self.deferred_moves,
            false => &mut self.moved_vars,
        };

        let var_name = mv.var_name();
        match target.get_mut(var_name) {
            Some(moves) => moves.push(mv),
            None => {
                target.insert(var_name.to_string(), vec![mv]);
            }
        };
    }

    /// Adds all moves from `moves` to the current scope. If `deferred` is true, the moves are
    /// added to the current scope as deferred moves.
    fn add_moves(&mut self, moves: HashMap<String, Vec<Move>>, deferred: bool) {
        for (_, new_moves) in moves {
            for new_move in new_moves {
                self.add_move(new_move, deferred);
            }
        }
    }
}

/// Checks a program to ensure that all moves of variables are legal and don't conflict.
pub struct MoveChecker<'a> {
    type_store: &'a TypeStore,
    errors: Vec<AnalyzeError>,
    stack: Vec<Scope>,
}

impl<'a> MoveChecker<'a> {
    /// Returns the analyzed type corresponding to the `type_key`.
    fn must_get_type(&self, type_key: TypeKey) -> &AType {
        self.type_store.must_get(type_key)
    }

    /// Pushes `scope` onto the stack.
    fn push_scope(&mut self, scope: Scope) {
        self.stack.push(scope);
    }

    /// Removes the current scope from the stack and returns it.
    fn pop_scope(&mut self) -> Scope {
        self.stack.pop().unwrap()
    }

    /// Returns a mutable reference to the current scope.
    fn cur_scope_mut(&mut self) -> &mut Scope {
        self.stack.last_mut().unwrap()
    }

    /// Adds the declared variable to the current scope. If this is a redeclaration of an existing
    /// variable by the same name that was also declared in this scope, this function will clear
    /// all moves of that variable from the current scope.
    fn add_declared_var(&mut self, var_name: &str) {
        let scope = self.cur_scope_mut();
        scope.clear_moves(var_name);
        scope.declared_vars.insert(var_name.to_string());
    }

    /// Records the move in the current scope.
    fn add_move(&mut self, mv: Move) {
        self.cur_scope_mut().add_move(mv, false);
    }

    /// Records `err`.
    fn add_err(&mut self, err: AnalyzeError) {
        self.errors.push(err);
    }

    /// If `to_loop_as_deferred` is true, merges moves as deferred moves into the enclosing loop
    /// scope. Otherwise, merges moves into the current scope. If `deferred_only` is true, only
    /// deferred moves will be copied.
    fn merge_moves_from(&mut self, scope: Scope, to_loop_as_deferred: bool, deferred_only: bool) {
        // Find the target scope into which we'll merge moves from the given scope.
        if to_loop_as_deferred {
            // Find the enclosing loop scope.
            for target_scope in self.stack.iter_mut().rev() {
                if target_scope.kind == ScopeKind::LoopBody {
                    // Copy moves as deferred moves from the given scope to the target scope.
                    target_scope.add_moves(scope.deferred_moves, true);
                    if !deferred_only {
                        target_scope.add_moves(scope.moved_vars, true);
                    }

                    break;
                }
            }
        } else {
            // Copy moves from the given scope to the current scope.
            let cur_scope = self.cur_scope_mut();
            cur_scope.add_moves(scope.deferred_moves, false);
            if !deferred_only {
                cur_scope.add_moves(scope.moved_vars, false);
            }
        };
    }

    /// Returns true if the current scope either is a loop body or exists inside a loop body and
    /// is guaranteed to execute inside that loop at most once. In other words, returns true if, no
    /// matter what happens at runtime, the code in the current scope will never be executed as part
    /// of a loop more than once.
    fn cur_scope_executes_at_most_once(&self) -> bool {
        // For each scope up to and including the loop body, if the scope exits the loop, it's
        // guaranteed to execute at most once.
        let mut exits_loop = false;
        for scope in self.stack.iter().rev() {
            if scope.exits_loop() {
                exits_loop = true;
            }

            if scope.kind == ScopeKind::LoopBody {
                if !exits_loop {
                    return false;
                }

                exits_loop = false;
            }
        }

        true
    }

    /// Returns true only if `var` was declared inside the current scope.
    fn var_declared_in_cur_scope(&self, var: &ASymbol) -> bool {
        self.stack
            .last()
            .unwrap()
            .declared_vars
            .contains(var.name.as_str())
    }

    /// Recursively performs move checks on `prog`.
    pub fn check_prog(prog: &AProgram, type_store: &TypeStore) -> Vec<AnalyzeError> {
        let mut move_checker = MoveChecker {
            type_store,
            errors: vec![],
            stack: vec![],
        };

        for statement in &prog.statements {
            move_checker.check_statement(statement);
        }

        move_checker.errors
    }

    /// Recursively performs move checks on `statement`.
    fn check_statement(&mut self, statement: &AStatement) {
        match statement {
            AStatement::StructTypeDeclaration(_)
            | AStatement::EnumTypeDeclaration(_)
            | AStatement::ExternFns(_)
            | AStatement::Consts(_)
            | AStatement::Continue
            | AStatement::Break => {
                // Nothing to do here since moves cannot occur in these types of statements.
            }

            AStatement::Loop(loop_body) => self.check_loop(loop_body),

            AStatement::FunctionDeclaration(fn_decl) => self.check_fn_decl(fn_decl),

            AStatement::VariableDeclaration(var_decl) => self.check_var_decl(var_decl),

            AStatement::VariableAssignment(assign) => self.check_var_assign(assign),

            AStatement::FunctionCall(call) => self.check_fn_call(call),

            AStatement::Return(ret) => self.check_ret(ret),

            AStatement::Closure(closure) => self.check_closure(closure),

            AStatement::Conditional(cond) => self.check_cond(cond),

            AStatement::Impl(impl_) => self.check_impl(impl_),
        }
    }

    /// Recursively checks all member functions inside an `impl` block.
    fn check_impl(&mut self, impl_: &AImpl) {
        for mem_fn in &impl_.member_fns {
            self.check_fn_decl(&mem_fn);
        }
    }

    /// Recursively performs move checks on `loop_body`.
    fn check_loop(&mut self, loop_body: &AClosure) {
        // Push a new scope for the loop body.
        self.push_scope(Scope::new(
            ScopeKind::LoopBody,
            loop_body.has_return,
            loop_body.has_break,
        ));

        // Check the loop body.
        self.check_statements(&loop_body.statements);

        // Pop the scope now that we're done checking the loop body.
        let scope = self.pop_scope();

        // If this loop is guaranteed to return, only merge its deferred moves. Otherwise, merge
        // all its moves.
        self.merge_moves_from(scope, false, loop_body.has_return);
    }

    /// Recursively performs move checks on `fn_decl`.
    fn check_fn_decl(&mut self, fn_decl: &AFn) {
        // Push a new scope onto the stack for the function body.
        self.push_scope(Scope::new_fn_body());

        // Perform move analysis on the function body.
        self.check_statements(&fn_decl.body.statements);

        // Pop the scope from the stack now that we're done checking the function body.
        self.pop_scope();
    }

    /// Recursively performs move checks on `var_decl`.
    fn check_var_decl(&mut self, var_decl: &AVarDecl) {
        // Check the expression being assigned to the variable.
        self.check_expr(&var_decl.val.kind);

        // Track the declaration in the current scope.
        self.add_declared_var(var_decl.name.as_str());
    }

    /// Recursively performs move checks on `assign`.
    fn check_var_assign(&mut self, assign: &AVarAssign) {
        // Check if the value being assigned is a variable and, if so, track its movement.
        self.check_expr(&assign.val.kind);
    }

    /// Recursively performs move checks on `call`.
    fn check_fn_call(&mut self, call: &AFnCall) {
        // Check if any of the function arguments are being moved.
        for arg in &call.args {
            self.check_expr(&arg.kind);
        }
    }

    /// Recursively performs move checks on `ret`.
    fn check_ret(&mut self, ret: &ARet) {
        // Check if we're moving the return value.
        match &ret.val {
            Some(val) => self.check_expr(&val.kind),
            None => {}
        }
    }

    /// Recursively performs move checks on `expr`.
    fn check_expr(&mut self, kind: &AExprKind) {
        match kind {
            AExprKind::Symbol(var) => {
                self.check_var(var);
            }
            AExprKind::FunctionCall(call) => {
                self.check_fn_call(call);
            }
            AExprKind::BinaryOperation(left, op, right) => {
                // Comparisons should not cause moves of their immediate operands since they don't
                // require copying data.
                let skip_left_check = op.is_comparator() && left.kind.is_symbol();
                let skip_right_check = op.is_comparator() && right.kind.is_symbol();

                if !skip_left_check {
                    self.check_expr(&left.kind)
                };

                if !skip_right_check {
                    self.check_expr(&right.kind)
                };
            }
            AExprKind::UnaryOperation(_, expr) => {
                self.check_expr(&expr.kind);
            }
            AExprKind::StructInit(struct_init) => {
                self.check_struct_init(struct_init);
            }
            _ => {}
        }
    }

    /// Recursively performs move checks on `struct_init`.
    fn check_struct_init(&mut self, struct_init: &AStructInit) {
        for (_, expr) in &struct_init.field_values {
            self.check_expr(&expr.kind);
        }
    }

    /// Recursively performs move checks on `closure`.
    fn check_closure(&mut self, closure: &AClosure) {
        // Push a new scope onto the stack for this closure.
        self.push_scope(Scope::new(
            ScopeKind::InlineClosure,
            closure.has_return,
            closure.has_break,
        ));

        self.check_statements(&closure.statements);

        // Now that we're done checking the closure, pop its scope from the stack and merge any
        // moves that occurred within it into the current scope.
        let scope = self.pop_scope();

        // If this closure if guaranteed to return, only merge its deferred moves into the current
        // scope. We do this because its regular moves should never conflict with later moves.
        self.merge_moves_from(scope, false, closure.has_return);
    }

    /// Recursively performs move checks on all statements in `statements`.
    fn check_statements(&mut self, statements: &Vec<AStatement>) {
        for statement in statements {
            self.check_statement(statement);
        }
    }

    /// Recursively performs move checks on all branches in `cond`.
    fn check_cond(&mut self, cond: &ACond) {
        // Check moves on each branch separately – that is, independently, because branch bodies
        // are mutually exclusive so their moves should never conflict with one another.
        let mut branch_scopes = vec![];
        for branch in &cond.branches {
            // Push a new scope for the branch body.
            self.push_scope(Scope::new(
                ScopeKind::BranchBody,
                branch.body.has_return,
                branch.body.has_break,
            ));

            // Check the branch body.
            self.check_statements(&branch.body.statements);

            // Pop the scope now that we're done checking the branch body. We don't want to merge
            // the moves from this branch into the parent scope yet, because we won't want them
            // to conflict with moves from other mutually exclusive branches in this conditional.
            branch_scopes.push(self.pop_scope());
        }

        // Copy the moves from the checked branch scopes to some parent scope.
        for branch_scope in branch_scopes {
            // If the branch breaks the loop, we need to merge its moves into the enclosing loop
            // scope as deferred moves. This way, the moves on this branch won't conflict with
            // any later moves inside the current loop, but they may conflict with moves after
            // the current loop.
            let to_loop_as_deferred = branch_scope.has_break;

            // If the branch returns, we should only merge its deferred moves, as none of its
            // regular moves could ever conflict with later moves.
            let deferred_only = branch_scope.has_return;
            self.merge_moves_from(branch_scope, to_loop_as_deferred, deferred_only);
        }
    }

    /// Performs move checks on `var`.
    fn check_var(&mut self, var: &ASymbol) {
        // Skip the move check entirely if the root variable is of some type that doesn't require
        // moves, or if it's a constant.
        if !self.must_get_type(var.parent_type_key).requires_move() || var.is_const {
            return;
        }

        // Search every scope in the stack for moves of this variable.
        let mv = Move::from(var);
        let mut errors = vec![];
        for scope in self.stack.iter_mut().rev() {
            // Check if the move conflicts with an existing move for this variable inside this
            // scope.
            for conflicting_move in scope.get_conflicting_moves(&mv) {
                errors.push(
                    AnalyzeError::new(
                        ErrorKind::UseOfMovedValue,
                        format_code!(
                            "cannot use {} because {} was already moved",
                            var,
                            conflicting_move
                        )
                            .as_str(),
                        &mv,
                    )
                        .with_detail(
                            format!(
                                "The conflicting move occurs at {}:{} because {} is not copied \
                                automatically.",
                                conflicting_move.start_pos.line,
                                conflicting_move.start_pos.col,
                                format_code!(conflicting_move),
                            )
                                .as_str(),
                        )
                        .with_help(format!(
                            "Consider either copying {} on line {} instead of moving it, or refactoring \
                            your code to avoid the move conflict.",
                            format_code!(conflicting_move), conflicting_move.start_pos.line
                        ).as_mut()),
                );
            }

            // Break as soon as we've checked up to the scope in which the variable was declared.
            if scope.declared_vars.contains(var.name.as_str()) {
                break;
            }
        }

        // If errors occurred, record them and return early. We're doing this here to avoid
        // borrowing issues above.
        if !errors.is_empty() {
            for err in errors {
                self.add_err(err);
            }

            return;
        }

        // If we're inside a loop and the current closure in which the move occurs is not
        // guaranteed to exit the loop (i.e. is not guaranteed to execute at most once), then the
        // move is illegal as it could execute more than once.
        if !self.var_declared_in_cur_scope(var) && !self.cur_scope_executes_at_most_once() {
            self.add_err(
                AnalyzeError::new(
                    ErrorKind::UseOfMovedValue,
                    format_code!("move of {} may occur multiple times inside a loop", var).as_str(),
                    &mv,
                )
                .with_detail(
                    format_code!(
                        "Duplicate moves of {} may occur because it is used \
                        inside a part of a loop that that may execute more than once.",
                        var,
                    )
                    .as_str(),
                )
                .with_help(
                    format_code!(
                        "Consider performing this move outside the loop, or in a part of \
                        the loop that is guaranteed to execute at most once (i.e. a part that will \
                        either {} or {}).",
                        "break",
                        "return",
                    )
                    .as_str(),
                ),
            );
            return;
        }

        // Only record a move if the type of the value being used requires a move. Some
        // basic types like bools and numerics are always copied instead of being moved.
        if self.must_get_type(var.get_type_key()).requires_move() {
            self.add_move(mv);
        }
    }
}
