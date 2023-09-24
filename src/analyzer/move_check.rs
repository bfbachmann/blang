use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::analyzer::closure::RichClosure;
use crate::analyzer::cond::RichCond;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExprKind;
use crate::analyzer::func::{RichFn, RichFnCall, RichRet};
use crate::analyzer::prog_context::ScopeKind;
use crate::analyzer::program::RichProg;
use crate::analyzer::r#struct::RichStructInit;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::analyzer::statement::RichStatement;
use crate::analyzer::var::RichVar;
use crate::analyzer::var_assign::RichVarAssign;
use crate::analyzer::var_dec::RichVarDecl;
use crate::format_code;
use crate::lexer::pos::{Locatable, Position};

/// Represents the change in ownership of a variable or value.
#[derive(Clone)]
struct Move {
    path: Vec<String>,
    start_pos: Position,
    end_pos: Position,
}

impl Locatable for Move {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl Display for Move {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.path.join("."))
    }
}

impl Move {
    /// Creates a new move from `var`.
    fn from(var: &RichVar) -> Self {
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

    /// Returns true if the path represented by `prefix` it the same as or is a parent of this
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
    /// Will be true if the scope contains a statement like `break`, `continue`, or `return` that
    /// is guaranteed to exit the current loop.
    exits_loop: bool,
    /// Will be true if the scope is guaranteed to return.
    returns: bool,
}

impl Scope {
    /// Creates a new scope. `exits_loop` should be true if the scope directly contains a statement
    /// that would escape the loop it falls under (i.e. `break` or `return`).
    fn new(kind: ScopeKind, exits_loop: bool, returns: bool) -> Self {
        Scope {
            kind,
            declared_vars: HashSet::new(),
            moved_vars: HashMap::new(),
            exits_loop,
            returns,
        }
    }

    /// Creates a new scope representing a function body.
    fn new_fn_body() -> Self {
        Scope {
            kind: ScopeKind::FnBody,
            declared_vars: HashSet::new(),
            moved_vars: HashMap::new(),
            exits_loop: false,
            returns: true,
        }
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

    /// Adds `mv` to this scope.
    fn add_move(&mut self, var_name: &str, mv: Move) {
        match self.moved_vars.get_mut(var_name) {
            Some(moves) => moves.push(mv),
            None => {
                self.moved_vars.insert(var_name.to_string(), vec![mv]);
            }
        };
    }
}

/// Checks a program to ensure that all moves of variables are legal and don't conflict.
pub struct MoveChecker<'a> {
    types: &'a HashMap<TypeId, RichType>,
    errors: Vec<AnalyzeError>,
    stack: Vec<Scope>,
}

impl<'a> MoveChecker<'a> {
    /// Pushes `scope` onto the stack.
    fn push_scope(&mut self, scope: Scope) {
        self.stack.push(scope);
    }

    /// Removes the current scope from the stack and returns it.
    fn pop_scope(&mut self) -> Scope {
        self.stack.pop().unwrap()
    }

    /// Adds the declared variable to the current scope.
    fn add_declared_var(&mut self, var_name: &str) {
        self.stack
            .last_mut()
            .unwrap()
            .declared_vars
            .insert(var_name.to_string());
    }

    /// Records the move in the current scope.
    fn add_move(&mut self, mv: Move) {
        let var_name = mv.var_name().to_string();
        self.stack
            .last_mut()
            .unwrap()
            .add_move(var_name.as_str(), mv);
    }

    /// Records `err`.
    fn add_err(&mut self, err: AnalyzeError) {
        self.errors.push(err);
    }

    /// Copies all moves contained within `scope` into the current scope.
    fn merge_moves_from(&mut self, scope: Scope) {
        let cur_scope = self.stack.last_mut().unwrap();
        for (var_name, new_moves) in scope.moved_vars {
            if let Some(existing_moves) = cur_scope.moved_vars.get_mut(var_name.as_str()) {
                existing_moves.extend(new_moves);
            } else {
                cur_scope.moved_vars.insert(var_name, new_moves);
            }
        }
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
            if scope.exits_loop {
                exits_loop = true;
            }

            if scope.kind == ScopeKind::Loop {
                if !exits_loop {
                    return false;
                }

                exits_loop = false;
            }
        }

        true
    }

    /// Returns true only if `var` was declared inside the current scope.
    fn var_declared_in_cur_scope(&self, var: &RichVar) -> bool {
        self.stack
            .last()
            .unwrap()
            .declared_vars
            .contains(var.var_name.as_str())
    }

    /// Recursively performs move checks on `prog`.
    pub fn check_prog(prog: &RichProg, types: &HashMap<TypeId, RichType>) -> Vec<AnalyzeError> {
        let mut move_checker = MoveChecker {
            types,
            errors: vec![],
            stack: vec![],
        };

        for statement in &prog.statements {
            move_checker.check_statement(statement);
        }

        move_checker.errors
    }

    /// Recursively performs move checks on `statement`.
    fn check_statement(&mut self, statement: &RichStatement) {
        match statement {
            RichStatement::StructTypeDeclaration(_)
            | RichStatement::Continue
            | RichStatement::Break => {
                // Nothing to do here since moves cannot occur in these types of statements.
            }

            RichStatement::Loop(loop_body) => self.check_loop(loop_body),

            RichStatement::FunctionDeclaration(fn_decl) => self.check_fn_decl(fn_decl),

            RichStatement::VariableDeclaration(var_decl) => self.check_var_decl(var_decl),

            RichStatement::VariableAssignment(assign) => self.check_var_assign(assign),

            RichStatement::FunctionCall(call) => self.check_fn_call(call),

            RichStatement::Return(ret) => self.check_ret(ret),

            RichStatement::Closure(closure) => self.check_closure(closure),

            RichStatement::Conditional(cond) => self.check_cond(cond),
        }
    }

    /// Recursively performs move checks on `loop_body`.
    fn check_loop(&mut self, loop_body: &RichClosure) {
        // Push a new scope for the loop body.
        self.push_scope(Scope::new(
            ScopeKind::Loop,
            loop_body.exits_loop(),
            loop_body.has_return,
        ));

        // Check the loop body.
        self.check_statements(&loop_body.statements);

        // Pop the scope now that we're done checking the loop body.
        let scope = self.pop_scope();
        self.merge_moves_from(scope);
    }

    /// Recursively performs move checks on `fn_decl`.
    fn check_fn_decl(&mut self, fn_decl: &RichFn) {
        // Push a new scope onto the stack for the function body.
        self.push_scope(Scope::new_fn_body());

        // Perform move analysis on the function body.
        self.check_statements(&fn_decl.body.statements);

        // Pop the scope from the stack now that we're done checking the function body.
        self.pop_scope();
    }

    /// Recursively performs move checks on `var_decl`.
    fn check_var_decl(&mut self, var_decl: &RichVarDecl) {
        // Check the expression being assigned to the variable.
        self.check_expr(&var_decl.val.kind);

        // Track the declaration in the current scope.
        self.add_declared_var(var_decl.name.as_str())
    }

    /// Recursively performs move checks on `assign`.
    fn check_var_assign(&mut self, assign: &RichVarAssign) {
        // Check if the value being assigned is a variable and, if so, track its movement.
        self.check_expr(&assign.val.kind);
    }

    /// Recursively performs move checks on `fn_call`.
    fn check_fn_call(&mut self, call: &RichFnCall) {
        // Check if any of the function arguments are being moved.
        for arg in &call.args {
            self.check_expr(&arg.kind);
        }
    }

    /// Recursively performs move checks on `ret`.
    fn check_ret(&mut self, ret: &RichRet) {
        // Check if we're moving the return value.
        match &ret.val {
            Some(val) => self.check_expr(&val.kind),
            None => {}
        }
    }

    /// Recursively performs move checks on `expr`.
    fn check_expr(&mut self, kind: &RichExprKind) {
        match kind {
            RichExprKind::Variable(var) => {
                self.check_var(var);
            }
            RichExprKind::FunctionCall(call) => {
                self.check_fn_call(call);
            }
            RichExprKind::BinaryOperation(left, _, right) => {
                self.check_expr(&right.kind);
                self.check_expr(&left.kind);
            }
            RichExprKind::UnaryOperation(_, expr) => {
                self.check_expr(&expr.kind);
            }
            RichExprKind::StructInit(struct_init) => {
                self.check_struct_init(struct_init);
            }
            _ => {}
        }
    }

    /// Recursively performs move checks on `struct_init`.
    fn check_struct_init(&mut self, struct_init: &RichStructInit) {
        for (_, expr) in &struct_init.field_values {
            self.check_expr(&expr.kind);
        }
    }

    /// Recursively performs move checks on `closure`.
    fn check_closure(&mut self, closure: &RichClosure) {
        // Push a new scope onto the stack for this closure.
        self.push_scope(Scope::new(
            ScopeKind::Inline,
            closure.exits_loop(),
            closure.has_return,
        ));

        self.check_statements(&closure.statements);

        // Now that we're done checking the closure, pop its scope from the stack and merge any
        // moves that occurred within it into the current scope.
        let scope = self.pop_scope();
        self.merge_moves_from(scope);
    }

    /// Recursively performs move checks on all statements in `statements`.
    fn check_statements(&mut self, statements: &Vec<RichStatement>) {
        for statement in statements {
            self.check_statement(statement);
        }
    }

    /// Recursively performs move checks on all branches in `cond`.
    fn check_cond(&mut self, cond: &RichCond) {
        let mut branch_scopes = vec![];
        for branch in &cond.branches {
            // Push a new scope for the branch body.
            self.push_scope(Scope::new(
                ScopeKind::Branch,
                branch.body.exits_loop(),
                branch.body.has_return,
            ));

            // Check the branch body.
            self.check_statements(&branch.body.statements);

            // Pop the scope now that we're done checking the branch body.
            branch_scopes.push(self.pop_scope());
        }

        // Add all the moves from the checked branch scopes to the current scope as the branch
        // doesn't return, since it's possible that any (or even all) of them are actually executed
        // at runtime.
        for branch_scope in branch_scopes {
            if !branch_scope.returns {
                self.merge_moves_from(branch_scope);
            }
        }
    }

    /// Performs move checks on `var`.
    fn check_var(&mut self, var: &RichVar) {
        // Skip the move check entirely if the root variable is of some type that doesn't require
        // moves.
        if !self.types.get(&var.var_type_id).unwrap().requires_move() {
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
                    AnalyzeError::new_with_locatable(
                        ErrorKind::UseOfMovedValue,
                        format_code!(
                            "cannot use {} because {} was already moved",
                            var,
                            conflicting_move
                        )
                        .as_str(),
                        Box::new(mv.clone()),
                    )
                    .with_detail(
                        format!(
                            "The conflicting move of {} occurs at {}:{}.",
                            format_code!(conflicting_move),
                            conflicting_move.start_pos.line,
                            conflicting_move.start_pos.col,
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
            if scope.declared_vars.contains(var.var_name.as_str()) {
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
                AnalyzeError::new_with_locatable(
                    ErrorKind::UseOfMovedValue,
                    format_code!("move of {} may occur multiple times inside a loop", var).as_str(),
                    Box::new(mv),
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
        if self.types.get(var.get_type_id()).unwrap().requires_move() {
            self.add_move(mv);
        }
    }
}
