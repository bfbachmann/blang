use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Display, Formatter};
use std::usize;

use crate::analyzer::ast::array::AArrayInit;
use crate::analyzer::ast::closure::AClosure;
use crate::analyzer::ast::cond::ACond;
use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::fn_call::AFnCall;
use crate::analyzer::ast::func::AFn;
use crate::analyzer::ast::index::AIndex;
use crate::analyzer::ast::member::AMemberAccess;
use crate::analyzer::ast::module::AModule;
use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::ast::r#enum::AEnumVariantInit;
use crate::analyzer::ast::r#loop::ALoop;
use crate::analyzer::ast::r#struct::AStructInit;
use crate::analyzer::ast::ret::ARet;
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::ast::symbol::ASymbol;
use crate::analyzer::ast::tuple::ATupleInit;
use crate::analyzer::ast::var_assign::AVarAssign;
use crate::analyzer::ast::var_dec::AVarDecl;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::fmt::format_vec;
use crate::lexer::pos::{Locatable, Position};
use crate::locatable_impl;
use crate::parser::ast::op::Operator;

/// Represents an SSA statement.
struct MStatement {
    kind: MStatementKind,
}

impl Debug for MStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl Display for MStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl MStatement {
    /// Returns true if the statement is a terminator (i.e. jumps to another
    /// block or returns).
    fn is_terminator(&self) -> bool {
        matches!(
            self.kind,
            MStatementKind::BranchIf(_) | MStatementKind::Branch(_) | MStatementKind::Return(_)
        )
    }
}

/// Represents the manner in which a value is used in an SSA statement.
#[derive(Debug, PartialEq)]
enum UseKind {
    Borrow,
    Move,
}

/// Represents the result of an SSA statement. This essentially just points
/// to a statement in a block and is supposed to represent the result of the
/// computation in that statement.
#[derive(Debug, Clone, Copy)]
struct MResult {
    block_id: usize,
    statement_id: usize,
}

/// Represents a kind of SSA value. This can either be an immediate (constant)
/// value or the result of a computation from another SSA statement.
#[derive(Debug, Clone, Copy)]
enum MValueKind {
    Result(MResult),
    Immediate,
}

/// Represents an SSA value.
#[derive(Debug, Clone, Copy)]
struct MValue {
    kind: MValueKind,
}

impl Display for MValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            MValueKind::Immediate => write!(f, "imm"),
            MValueKind::Result(result) => {
                write!(f, "result({}, {})", result.block_id, result.statement_id)
            }
        }
    }
}

impl MValue {
    fn new_result(block_id: usize, statement_id: usize) -> MValue {
        MValue {
            kind: MValueKind::Result(MResult {
                block_id,
                statement_id,
            }),
        }
    }

    fn new_immediate() -> MValue {
        MValue {
            kind: MValueKind::Immediate,
        }
    }
}

/// Represents a variable declaration inside a function.
#[derive(Debug)]
struct MDeclare {
    var_name: String,
    value: MValue,
}

/// Represents an assignment to a variable inside a function.
#[derive(Debug)]
struct MAssign {
    target: String,
    value: MValue,
}

/// Represents a unary operation.
#[derive(Debug)]
struct MUnaryOp {
    // TODO: Not sure this field is necessary.
    op: Operator,
    operand: MValue,
}

/// Represents a binary operation.
#[derive(Debug)]
struct MBinaryOp {
    // TODO: Not sure this field is necessary.
    op: Operator,
    left_operand: MValue,
    right_operand: MValue,
}

/// Represents a GEP instruction (get a member of an existing value - essentially
/// pointer arithmetic).
#[derive(Debug)]
struct MGetMember {
    value: MValue,
    member_name: String,
}

/// Represents indexing into a collection (like an array).
#[derive(Debug)]
struct MIndex {
    collection: MValue,
    index: MValue,
}

/// Represents a function call with arguments.
#[derive(Debug)]
struct MCall {
    func: MValue,
    args: Vec<MValue>,
    has_return_val: bool,
}

/// Represents an unconditional branch instruction that jumps to another block.
#[derive(Debug)]
struct MBranch {
    target_block_id: usize,
}

/// Represents a condition branch instruction that will jump to one of two
/// blocks based on whether the branch condition is true.
#[derive(Debug)]
struct MBranchIf {
    condition: MValue,
    then_block_id: usize,
    else_block_id: usize,
}

/// Represents a return from a function. There should only ever be one return
/// statement on one block (the end block) per function.
#[derive(Debug)]
struct MReturn {
    maybe_value: Option<MValue>,
}

/// Represents a value that originates from one of many other blocks.
#[derive(Debug)]
struct MPhi {
    /// Maps predecessor block ID to the value that comes from that block.
    values: HashMap<usize, MValue>,
}

/// Represents a store statement - writing some value into memory.
#[derive(Debug)]
struct MStore {
    target: MValue,
    value: MValue,
}

/// Represents the borrowing of a value - essentially using a value by reference.
#[derive(Debug)]
struct MBorrow {
    var_name: String,
}

/// Represents the moving of a value (changing ownership).
#[derive(Debug, Clone)]
struct MMove {
    value_path: String,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(MMove);

/// Represents a kind of SSA statement.
enum MStatementKind {
    // Variable bindings
    Declare(MDeclare),
    Assign(MAssign),

    // Control blow
    Branch(MBranch),
    BranchIf(MBranchIf),
    Return(MReturn),

    // Operations
    Borrow(MBorrow),
    Move(MMove),
    UnaryOp(MUnaryOp),
    BinaryOp(MBinaryOp),
    Phi(MPhi),
    GetMember(MGetMember),
    Index(MIndex),
    Store(MStore),
    Call(MCall),
}

impl Debug for MStatementKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

// This is just here to help visualize control flow for debugging.
impl Display for MStatementKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            MStatementKind::Declare(declare) => {
                write!(f, "let {} = {}", declare.var_name, declare.value)
            }
            MStatementKind::Assign(assign) => {
                write!(f, "{} = {}", assign.target, assign.value)
            }
            MStatementKind::Branch(branch) => {
                write!(f, "branch {}", branch.target_block_id)
            }
            MStatementKind::BranchIf(branch_if) => {
                write!(
                    f,
                    "branchif {}, {}, {}",
                    branch_if.condition, branch_if.then_block_id, branch_if.else_block_id
                )
            }
            MStatementKind::Return(ret) => {
                write!(
                    f,
                    "return {}",
                    match ret.maybe_value {
                        Some(value) => format!("{value}"),
                        None => "void".to_string(),
                    }
                )
            }
            MStatementKind::Borrow(borrow) => {
                write!(f, "borrow {}", borrow.var_name)
            }
            MStatementKind::Move(mv) => {
                write!(f, "move {}", mv.value_path)
            }
            MStatementKind::UnaryOp(unary_op) => {
                write!(f, "{} {}", unary_op.op, unary_op.operand)
            }
            MStatementKind::BinaryOp(bin_op) => {
                write!(
                    f,
                    "{} {} {}",
                    bin_op.left_operand, bin_op.op, bin_op.right_operand
                )
            }
            MStatementKind::Phi(phi) => {
                write!(f, "phi ")?;
                for (src, val) in &phi.values {
                    write!(f, "({val} from {src}) ")?;
                }

                Ok(())
            }
            MStatementKind::GetMember(get_member) => {
                write!(
                    f,
                    "get_member {} from {}",
                    get_member.member_name, get_member.value
                )
            }
            MStatementKind::Index(index) => {
                write!(f, "{}.({})", index.collection, index.index)
            }
            MStatementKind::Store(store) => {
                write!(f, "store {} into {}", store.value, store.target)
            }
            MStatementKind::Call(call) => {
                write!(f, "call {}(", call.func)?;

                for arg in &call.args {
                    write!(f, "{}", arg)?;
                }

                write!(f, ")")
            }
        }
    }
}

/// Represents a basic block in a function. Blocks are composed of at least one
/// SSA statement and must end in a terminator.
struct Block {
    statements: Vec<MStatement>,
    predecessor_block_ids: Vec<usize>,
}

impl Debug for Block {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

// This is just here to help with debugging.
impl Display for Block {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let preds = format_vec(&self.predecessor_block_ids, ", ");
        writeln!(f, "(preds: {preds})")?;

        for (i, statement) in self.statements.iter().enumerate() {
            write!(f, "  {i}| {statement}\n")?;
        }

        Ok(())
    }
}

impl Block {
    fn new() -> Block {
        Block {
            statements: vec![],
            predecessor_block_ids: vec![],
        }
    }
}

/// Represents a unique scope inside a function.
struct MScope {
    variables: HashMap<String, MValue>,
    is_loop: bool,
    maybe_loop_end_block_id: Option<usize>,
    loop_update_block_id: usize,
}

impl MScope {
    fn new() -> MScope {
        MScope {
            variables: Default::default(),
            is_loop: false,
            maybe_loop_end_block_id: None,
            loop_update_block_id: 0,
        }
    }

    fn new_loop(loop_cond_block_id: usize, maybe_loop_end_block_id: Option<usize>) -> MScope {
        MScope {
            variables: Default::default(),
            is_loop: true,
            loop_update_block_id: loop_cond_block_id,
            maybe_loop_end_block_id,
        }
    }
}

/// Stores information about control flow and data flow within a function.
struct CFGAnalyzer<'a> {
    ctx: &'a mut ProgramContext,
    blocks: Vec<Block>,
    cur_block_id: usize,
    stack: Vec<MScope>,
    /// Maps block ID to the return value that comes from that block.
    return_values: HashMap<usize, MValue>,
}

impl Debug for CFGAnalyzer<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl Display for CFGAnalyzer<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (i, block) in self.blocks.iter().enumerate() {
            writeln!(f, "block {i}: {block}")?;
        }

        Ok(())
    }
}

impl CFGAnalyzer<'_> {
    /// Analyzes the control and data flow of `func`. In particular, this will
    /// check for use-after-move violations inside the function.
    fn analyze_fn(ctx: &mut ProgramContext, func: &AFn) {
        let mut analyzer = CFGAnalyzer {
            ctx,
            blocks: vec![Block::new(), Block::new()],
            cur_block_id: 0,
            stack: vec![MScope::new()],
            return_values: Default::default(),
        };

        analyzer.analyze_statements(&func.body.statements);

        // Jump to the end block from the current block if it does not have
        // a terminator.
        if !analyzer.cur_block_has_terminator() {
            analyzer.insert_statement(MStatement {
                kind: MStatementKind::Branch(MBranch {
                    target_block_id: analyzer.end_block_id(),
                }),
            });
        }

        analyzer.switch_to_block(analyzer.end_block_id());

        // If there are return values for this function, insert them into a
        // phi node and use that as the return value.
        let maybe_ret_val = if !analyzer.return_values.is_empty() {
            let ret_val = analyzer
                .insert_statement(MStatement {
                    kind: MStatementKind::Phi(MPhi {
                        values: analyzer.return_values.clone(),
                    }),
                })
                .unwrap();

            Some(ret_val)
        } else {
            None
        };

        analyzer.insert_statement(MStatement {
            kind: MStatementKind::Return(MReturn {
                maybe_value: maybe_ret_val,
            }),
        });

        // Now that the control flow graph for this function is complete,
        // we can check loops for duplicate moves. We do this by doing a BFS
        // over the entire function graph, doing DFS from each node to find
        // any cycles that begin and end with that node.
        let cycles: Vec<Vec<usize>> = analyzer
            .bfs(|block_id| analyzer.find_cycle(vec![block_id]))
            .into_iter()
            .filter_map(|v| v)
            .collect();

        for cycle in cycles {
            let illegal_moves: Vec<MMove> = analyzer
                .get_duplicated_moves_in_cycle(cycle)
                .into_values()
                .into_iter()
                .flatten()
                .collect();
            for illegal_move in illegal_moves {
                analyzer.ctx.insert_err(
                    AnalyzeError::new(
                        ErrorKind::UseOfMovedValue,
                        format_code!(
                            "move of {} may occur multiple times",
                            illegal_move.value_path,
                        )
                        .as_str(),
                        &illegal_move,
                    )
                    .with_detail(
                        format_code!(
                            "Move of {} may occur multiple times inside a loop.",
                            illegal_move.value_path
                        )
                        .as_str(),
                    )
                    .with_help(
                        format_code!(
                            "Consider copying or borrowing {} instead of \
                            moving it, or replace {} immediately after the move.",
                            illegal_move.value_path,
                            illegal_move.value_path,
                        )
                        .as_str(),
                    ),
                );
            }
        }

        // Uncomment to view CFG debug info.
        // print!("___ {} ___\n{analyzer}", module.path);
    }

    /// Checks the given cycle (a list of block IDs that forms a loop) for moves
    /// that may execute more than once (i.e., use-after-move errors).
    fn get_duplicated_moves_in_cycle(&self, cycle: Vec<usize>) -> HashMap<String, Vec<MMove>> {
        // Maps root variable name to the sequence of moves from the variable
        // in the cycle.
        let mut illegal_moves: HashMap<String, Vec<MMove>> = HashMap::new();

        fn drop_last_move(map: &mut HashMap<String, Vec<MMove>>, move_path: &str) {
            let root_var_name = get_root_var_name(move_path);
            if let Some(move_seq) = map.get_mut(root_var_name) {
                for (i, existing_mv) in move_seq.iter().rev().enumerate() {
                    if moves_conflict(existing_mv.value_path.as_str(), move_path) {
                        move_seq.remove(move_seq.len() - i - 1);
                        break;
                    }
                }
            }
        }

        fn add_move(map: &mut HashMap<String, Vec<MMove>>, mv: MMove) {
            let root_var_name = get_root_var_name(mv.value_path.as_str());
            if let Some(move_seq) = map.get_mut(root_var_name) {
                move_seq.push(mv);
            } else {
                map.insert(root_var_name.to_string(), vec![mv]);
            }
        }

        for block_id in cycle {
            for statement in &self.get_block(block_id).statements {
                match &statement.kind {
                    MStatementKind::Declare(declare) => {
                        drop_last_move(&mut illegal_moves, declare.var_name.as_str());
                    }

                    MStatementKind::Assign(assign) => {
                        drop_last_move(&mut illegal_moves, assign.target.as_str());
                    }

                    MStatementKind::Move(mv) => {
                        add_move(&mut illegal_moves, mv.clone());
                    }

                    _ => {}
                }
            }
        }

        illegal_moves
    }

    /// Traverses the control-flow graph breadth-first, calling
    /// `visitor` with each block's ID and accumulating the results it returns.
    fn bfs<T, R>(&self, visitor: T) -> Vec<R>
    where
        T: Fn(usize) -> R,
    {
        let mut tracked_block_ids = HashSet::from([0]);
        let mut block_ids_to_check = VecDeque::from([0]);
        let mut results = vec![];

        while let Some(block_id) = block_ids_to_check.pop_front() {
            results.push(visitor(block_id));

            let last_statement = self.get_block(block_id).statements.last().unwrap();
            let next_block_ids = match &last_statement.kind {
                MStatementKind::Branch(branch) => {
                    vec![branch.target_block_id]
                }
                MStatementKind::BranchIf(branch_if) => {
                    vec![branch_if.then_block_id, branch_if.else_block_id]
                }
                _ => {
                    vec![]
                }
            };

            for next_block_id in next_block_ids {
                if tracked_block_ids.insert(next_block_id) {
                    block_ids_to_check.push_back(next_block_id);
                }
            }
        }

        results
    }

    /// Returns the current block.
    fn cur_block(&self) -> &Block {
        self.blocks.get(self.cur_block_id).unwrap()
    }

    /// Returns a mutable reference to the current block.
    fn cur_block_mut(&mut self) -> &mut Block {
        self.blocks.get_mut(self.cur_block_id).unwrap()
    }

    /// Returns the ID of the end block for this function.
    fn end_block_id(&self) -> usize {
        1
    }

    /// Adds the current block's ID as a predecessor of the given block.
    fn link_block(&mut self, block_id: usize) {
        let cur_block_id = self.cur_block_id;
        self.get_block_mut(block_id)
            .predecessor_block_ids
            .push(cur_block_id);
    }

    /// Tracks the variable with the given name in current scope on the stack.
    fn insert_variable(&mut self, name: String, value: MValue) {
        self.stack.last_mut().unwrap().variables.insert(name, value);
    }

    /// Appends the given statement to the end of the current block. This will
    /// also add any necessary predecessors block IDs to target blocks if the
    /// statement is a branch statement. Returns a value representing the result
    /// of `statement` if it would yield a result (i.e. is not a terminator).
    fn insert_statement(&mut self, statement: MStatement) -> Option<MValue> {
        // Make sure we're not adding a statement to a block after it already
        // has a terminator.
        assert!(
            !self.cur_block_has_terminator(),
            "cannot insert statement after terminator"
        );

        let maybe_value = match &statement.kind {
            MStatementKind::Branch(branch) => {
                self.link_block(branch.target_block_id);
                None
            }

            MStatementKind::BranchIf(branch) => {
                self.link_block(branch.then_block_id);
                self.link_block(branch.else_block_id);
                None
            }

            MStatementKind::Return(_) => None,

            // Calls yield no result if they have no return value.
            MStatementKind::Call(call) if !call.has_return_val => None,

            // Every other kind of statement should yield some result.
            _ => Some(MValue::new_result(
                self.cur_block_id,
                self.cur_block_mut().statements.len(),
            )),
        };

        self.cur_block_mut().statements.push(statement);

        maybe_value
    }

    /// Gets the block with the given ID.
    fn get_block(&self, block_id: usize) -> &Block {
        self.blocks.get(block_id).unwrap()
    }

    /// Gets a mutable reference to the block with the given ID.
    fn get_block_mut(&mut self, block_id: usize) -> &mut Block {
        self.blocks.get_mut(block_id).unwrap()
    }

    /// Creates a new block and returns its ID.
    fn new_block(&mut self) -> usize {
        self.blocks.push(Block::new());
        self.blocks.len() - 1
    }

    /// Sets the current block ID to `block_id`.
    fn switch_to_block(&mut self, block_id: usize) {
        self.cur_block_id = block_id;
    }

    /// Returns true if the current block ends with a terminator statement.
    fn cur_block_has_terminator(&self) -> bool {
        self.cur_block()
            .statements
            .last()
            .is_some_and(|s| s.is_terminator())
    }

    /// Analyzes the given statements, adding them to the control flow graph.
    fn analyze_statements(&mut self, statements: &Vec<AStatement>) {
        for (i, statement) in statements.iter().enumerate() {
            self.analyze_statement(statement);

            // Don't continue if the current block already has a terminator
            // and this is not the last statement. This is a case of unreachable
            // code.
            let is_last = i + 1 == statements.len();
            if self.cur_block_has_terminator() && !is_last {
                // TODO: Use correct statement location in dead code warning.
                // self.ctx.insert_warn(AnalyzeWarning::new(
                //     WarnKind::UnreachableCode,
                //     "unreachable code",
                //     &statement,
                // ));

                break;
            }
        }
    }

    /// Analyzes `statement`, adding it to the control flow graph.
    fn analyze_statement(&mut self, statement: &AStatement) {
        match statement {
            AStatement::VariableDeclaration(var_decl) => {
                self.analyze_var_decl(var_decl);
            }

            AStatement::VariableAssignment(var_assign) => {
                self.analyze_var_assign(var_assign);
            }

            AStatement::Const(const_decl) => {
                self.analyze_const_decl(const_decl);
            }

            AStatement::FunctionCall(fn_call) => {
                self.analyze_fn_call(fn_call);
            }

            AStatement::FunctionDeclaration(func) => {
                self.analyze_fn_decl(func);
            }

            AStatement::Closure(closure) => {
                self.analyze_closure(closure);
            }

            AStatement::Conditional(cond) => {
                self.analyze_cond(cond);
            }
            AStatement::Loop(loop_) => self.analyze_loop(loop_),

            AStatement::Break => self.analyze_break(),

            AStatement::Continue => self.analyze_continue(),

            AStatement::Return(ret) => self.analyze_return(ret),

            // These statements don't affect control flow.
            AStatement::StructTypeDeclaration(_)
            | AStatement::EnumTypeDeclaration(_)
            | AStatement::ExternFn(_)
            | AStatement::Impl(_) => {}
        }
    }

    /// Analyzes the given loop, adding it to the control flow graph.
    fn analyze_loop(&mut self, loop_: &ALoop) {
        // Analyze the loop init statement if there is one.
        if let Some(init_statement) = &loop_.maybe_init {
            self.analyze_statement(init_statement);
        }

        // Return early if the loop init statement branches away from the loop,
        // thereby making the rest of the loop code unreachable.
        if self.cur_block_has_terminator() {
            // TODO: Insert dead code warning.
            return;
        }

        // Create a loop condition block and switch to it.
        let cond_block_id = self.new_block();
        self.insert_statement(MStatement {
            kind: MStatementKind::Branch(MBranch {
                target_block_id: cond_block_id,
            }),
        });

        let body_block_id = self.new_block();
        let mut maybe_end_block_id = None;

        // Analyze branch statement based on condition (or lack thereof).
        self.switch_to_block(cond_block_id);
        if let Some(cond) = &loop_.maybe_cond {
            let cond_val = self.analyze_expr(cond, UseKind::Move);
            maybe_end_block_id = Some(self.new_block());
            self.insert_statement(MStatement {
                kind: MStatementKind::BranchIf(MBranchIf {
                    condition: cond_val,
                    then_block_id: body_block_id,
                    else_block_id: maybe_end_block_id.unwrap(),
                }),
            });
        } else {
            self.insert_statement(MStatement {
                kind: MStatementKind::Branch(MBranch {
                    target_block_id: body_block_id,
                }),
            });
        }

        // Analyze the update block. If there is an update statement, include it
        // in the update block.
        let update_block_id = self.new_block();
        self.switch_to_block(update_block_id);
        if let Some(update) = &loop_.maybe_update {
            self.analyze_statement(update);
        }

        // Append an unconditional branch back to the conditional block, if necessary.
        if !self.cur_block_has_terminator() {
            self.insert_statement(MStatement {
                kind: MStatementKind::Branch(MBranch {
                    target_block_id: cond_block_id,
                }),
            });
        }

        // Analyze the loop body.
        self.stack
            .push(MScope::new_loop(update_block_id, maybe_end_block_id));
        self.switch_to_block(body_block_id);
        self.analyze_statements(&loop_.body.statements);

        // Append an unconditional branch to the loop update block (equivalent
        // to a `continue` statement), if necessary.
        if !self.cur_block_has_terminator() {
            self.analyze_continue();
        }

        // Jump to the end block now that the loop is done.
        if let Some(end_block_id) = self.stack.pop().unwrap().maybe_loop_end_block_id {
            self.switch_to_block(end_block_id);
        }
    }

    /// Looks for the ID of the end block of the current loop. If the current
    /// loop does not yet have an end block, this will create one and return it.
    /// Panics if we're not inside a loop.
    fn get_loop_end_block_id(&mut self) -> usize {
        let end_block_id = match self
            .get_cur_loop_scope_mut()
            .maybe_loop_end_block_id
            .clone()
        {
            Some(end_block_id) => end_block_id,
            None => self.new_block(),
        };

        self.get_cur_loop_scope_mut().maybe_loop_end_block_id = Some(end_block_id);
        end_block_id
    }

    /// Looks for the ID of the current loop's update block (i.e. the block to
    /// jump to when we encounter a `continue` statement in the loop).
    /// Panics if we're not in side a loop.
    fn get_loop_update_block_id(&mut self) -> usize {
        let scope = self.get_cur_loop_scope_mut();
        scope.loop_update_block_id
    }

    /// Return a mutable reference to the current loop scope. Panics if we're
    /// not inside a loop.
    fn get_cur_loop_scope_mut(&mut self) -> &mut MScope {
        for scope in self.stack.iter_mut().rev() {
            if scope.is_loop {
                return scope;
            }
        }

        panic!("not inside a loop")
    }

    /// Adds a break to the current loop in the control flow graph.
    fn analyze_break(&mut self) {
        let end_block_id = self.get_loop_end_block_id();
        self.insert_statement(MStatement {
            kind: MStatementKind::Branch(MBranch {
                target_block_id: end_block_id,
            }),
        });
    }

    /// Adds a jump back to the beginning to the current loop in the control
    /// flow graph.
    fn analyze_continue(&mut self) {
        let update_block_id = self.get_loop_update_block_id();
        self.insert_statement(MStatement {
            kind: MStatementKind::Branch(MBranch {
                target_block_id: update_block_id,
            }),
        });
    }

    /// Analyzes a return statement. A return is graphed as a jump to the function's
    /// end block.
    fn analyze_return(&mut self, ret: &ARet) {
        // Record the return value, if there is one.
        if let Some(expr) = &ret.val {
            let val = self.analyze_expr(expr, UseKind::Move);
            self.return_values.insert(self.cur_block_id, val);
        }

        self.insert_statement(MStatement {
            kind: MStatementKind::Branch(MBranch {
                target_block_id: self.end_block_id(),
            }),
        });
    }

    /// Analyzes a conditional statement.
    fn analyze_cond(&mut self, cond: &ACond) {
        let mut maybe_end_block_id = None;

        // This function will check if the block we're on already has a terminator.
        // If not, we need it to branch to the end of the conditional.
        fn ensure_terminator(
            analyzer: &mut CFGAnalyzer,
            maybe_end_block_id: &mut Option<usize>,
            block_id_to_use: Option<usize>,
        ) {
            if analyzer.cur_block_has_terminator() {
                return;
            }

            if maybe_end_block_id.is_none() {
                *maybe_end_block_id = if block_id_to_use.is_some() {
                    block_id_to_use
                } else {
                    Some(analyzer.new_block())
                };
            }

            let end_block_id = maybe_end_block_id.unwrap();
            analyzer.insert_statement(MStatement {
                kind: MStatementKind::Branch(MBranch {
                    target_block_id: end_block_id,
                }),
            });
        }

        for (i, branch) in cond.branches.iter().enumerate() {
            let is_last_branch = i == cond.branches.len() - 1;

            if let Some(cond) = &branch.cond {
                let condition = self.analyze_expr(cond, UseKind::Move);
                let then_block_id = self.new_block();
                let else_block_id = self.new_block();

                self.insert_statement(MStatement {
                    kind: MStatementKind::BranchIf(MBranchIf {
                        condition,
                        then_block_id,
                        else_block_id,
                    }),
                });

                self.switch_to_block(then_block_id);
                self.stack.push(MScope::new());
                self.analyze_statements(&branch.body.statements);
                ensure_terminator(
                    self,
                    &mut maybe_end_block_id,
                    match is_last_branch {
                        true => Some(else_block_id),
                        false => None,
                    },
                );
                self.stack.pop();

                self.switch_to_block(else_block_id);
            } else {
                self.stack.push(MScope::new());
                self.analyze_statements(&branch.body.statements);
                ensure_terminator(self, &mut maybe_end_block_id, None);
                self.stack.pop();
            }
        }

        if let Some(end_block_id) = maybe_end_block_id {
            self.switch_to_block(end_block_id);
        }
    }

    /// Analyzes a function declaration.
    fn analyze_fn_decl(&mut self, fn_decl: &AFn) {
        self.insert_statement(MStatement {
            kind: MStatementKind::Declare(MDeclare {
                var_name: fn_decl.signature.mangled_name.clone(),
                value: MValue::new_immediate(),
            }),
        });

        // Analyze the nested function.
        CFGAnalyzer::analyze_fn(self.ctx, fn_decl);
    }

    /// Analyzes a variable declaration.
    fn analyze_var_decl(&mut self, var_decl: &AVarDecl) {
        let value = self.analyze_expr(&var_decl.val, UseKind::Move);
        let result = self
            .insert_statement(MStatement {
                kind: MStatementKind::Declare(MDeclare {
                    var_name: var_decl.name.clone(),
                    value,
                }),
            })
            .unwrap();

        self.insert_variable(var_decl.name.clone(), result);
    }

    /// Analyzes a symbol that is used in an SSA expression.
    fn analyze_symbol(&mut self, symbol: &ASymbol, use_kind: UseKind) -> MValue {
        if symbol.is_const | symbol.is_method {
            return MValue::new_immediate();
        }

        // At this point we know the symbol represents a local variable. We need
        // to locate the statement where the variable was defined.
        let type_moves = self.ctx.must_get_type(symbol.type_key).requires_move();
        return if type_moves && use_kind == UseKind::Move {
            self.insert_statement(MStatement {
                kind: MStatementKind::Move(MMove {
                    value_path: symbol.name.clone(),
                    start_pos: symbol.start_pos().clone(),
                    end_pos: symbol.end_pos().clone(),
                }),
            })
            .unwrap()
        } else {
            self.insert_statement(MStatement {
                kind: MStatementKind::Borrow(MBorrow {
                    var_name: symbol.name.clone(),
                }),
            })
            .unwrap()
        };
    }

    /// Analyzes the access of a member on some value in an SSA statement.
    fn analyze_member_access(&mut self, access: &AMemberAccess, use_kind: UseKind) -> MValue {
        if access.is_method || access.base_expr.kind.is_type() {
            return MValue::new_immediate();
        }

        // Change the use kind to a borrow if the member type doesn't move.
        let member_type_moves = self
            .ctx
            .must_get_type(access.member_type_key)
            .requires_move();
        let use_kind = match member_type_moves {
            true => use_kind,
            false => UseKind::Borrow,
        };

        let base_value = self.analyze_expr(&access.base_expr, use_kind);
        self.insert_statement(MStatement {
            kind: MStatementKind::GetMember(MGetMember {
                value: base_value,
                member_name: access.member_name.to_string(),
            }),
        })
        .unwrap()
    }

    /// Analyzes the indexing into some collection.
    fn analyze_index(&mut self, index: &AIndex, mut use_kind: UseKind) -> MValue {
        let result_is_moved = self
            .ctx
            .must_get_type(index.result_type_key)
            .requires_move();
        if use_kind == UseKind::Move && !result_is_moved {
            use_kind = UseKind::Borrow;
        }

        let index_val = self.analyze_expr(&index.index_expr, UseKind::Move);
        let collection = self.analyze_expr(&index.collection_expr, use_kind);
        self.insert_statement(MStatement {
            kind: MStatementKind::Index(MIndex {
                collection,
                index: index_val,
            }),
        })
        .unwrap()
    }

    /// Analyzes a function call.
    fn analyze_fn_call(&mut self, call: &AFnCall) -> Option<MValue> {
        let args: Vec<MValue> = call
            .args
            .iter()
            .map(|arg| self.analyze_expr(arg, UseKind::Move))
            .collect();
        let func = self.analyze_expr(&call.fn_expr, UseKind::Move);
        let has_return_val = call.maybe_ret_type_key.is_some();

        self.insert_statement(MStatement {
            kind: MStatementKind::Call(MCall {
                func,
                args,
                has_return_val,
            }),
        })
    }

    // Analyzes struct initialization.
    fn analyze_struct_init(&mut self, struct_init: &AStructInit) -> MValue {
        for field_val in struct_init.field_values.values() {
            self.analyze_expr(field_val, UseKind::Move);
        }

        // We're going to treat the new struct value as an immediate for now,
        // since technically it's a brand-new value. In reality, however, this
        // value is just a pointer to some region of the stack where we wrote
        // field values.
        MValue::new_immediate()
    }

    /// Analyzes enum initialization.
    fn analyze_enum_init(&mut self, enum_init: &AEnumVariantInit) -> MValue {
        if let Some(val) = &enum_init.maybe_value {
            self.analyze_expr(val, UseKind::Move);
        }

        // See comment in `analyze_struct_init` about this being an immediate
        // value.
        MValue::new_immediate()
    }

    /// Analyzes tuple initialization.
    fn analyze_tuple_init(&mut self, tuple_init: &ATupleInit) -> MValue {
        for field_val in &tuple_init.values {
            self.analyze_expr(field_val, UseKind::Move);
        }

        // See comment in `analyze_struct_init` about this being an immediate
        // value.
        MValue::new_immediate()
    }

    /// Analyzes array initialization. Note that array initialization is special
    /// because, in some cases, it actually represents a loop that writes a value
    /// into memory.
    fn analyze_array_init(&mut self, array_init: &AArrayInit) -> MValue {
        // Jump to a new block for array initialization. We're doing this because
        // array initialization may require a loop.
        let array_init_block_id = self.new_block();
        self.insert_statement(MStatement {
            kind: MStatementKind::Branch(MBranch {
                target_block_id: array_init_block_id,
            }),
        });

        self.switch_to_block(array_init_block_id);

        for val in &array_init.values {
            self.analyze_expr(val, UseKind::Move);
        }

        // If the value being written into the array is repeated more than once
        // we'll have this array init block loop back on itself.
        let value_repeats = array_init.maybe_repeat_count.is_some_and(|count| count > 1);
        if value_repeats {
            let end_block_id = self.new_block();
            self.insert_statement(MStatement {
                kind: MStatementKind::BranchIf(MBranchIf {
                    condition: MValue::new_immediate(),
                    then_block_id: array_init_block_id,
                    else_block_id: end_block_id,
                }),
            });

            self.switch_to_block(end_block_id);
        }

        // See comment in `analyze_struct_init` about this being an immediate
        // value.
        MValue::new_immediate()
    }

    /// Analyzes an anonymous function.
    fn analyze_anon_fn(&mut self, func: &AFn) -> MValue {
        CFGAnalyzer::analyze_fn(self.ctx, func);
        MValue::new_immediate()
    }

    /// Analyzes a unary operation.
    fn analyze_unary_op(&mut self, op: &Operator, operand: &AExpr, use_kind: UseKind) -> MValue {
        let use_kind = match op {
            Operator::Reference | Operator::MutReference => UseKind::Borrow,
            Operator::LogicalNot | Operator::Subtract => use_kind,
            Operator::Defererence => {
                // Check if the value being dereferenced is a shared reference
                // to a value that requires moves. If so, this is an illegal
                // operation.
                let operand_type = self.ctx.must_get_type(operand.type_key);
                if use_kind == UseKind::Move
                    && operand_type.is_ptr()
                    && self
                        .ctx
                        .must_get_type(operand_type.to_ptr_type().pointee_type_key)
                        .requires_move()
                {
                    self.ctx.insert_err(
                        AnalyzeError::new(
                            ErrorKind::IllegalMove,
                            format_code!(
                                "cannot move out of shared reference {}",
                                operand.display(self.ctx)
                            )
                            .as_str(),
                            operand,
                        )
                        .with_detail(
                            "This move is illegal because it it happens via a \
                            shared reference, so the underlying value is not owned.",
                        )
                        .with_help(
                            "Consider copying the value via the reference \
                            and use that copy instead.",
                        ),
                    );
                }

                UseKind::Move
            }
            _ => panic!("unexpected unary operand {op}"),
        };

        let operand_val = self.analyze_expr(operand, use_kind);

        self.insert_statement(MStatement {
            kind: MStatementKind::UnaryOp(MUnaryOp {
                op: op.clone(),
                operand: operand_val,
            }),
        })
        .unwrap()
    }

    /// Analyzes a binary operation.
    fn analyze_binary_op(&mut self, op: &Operator, left: &AExpr, right: &AExpr) -> MValue {
        if op.is_logical() {
            // Logical operations need special handling because they short-circuit,
            // which affects control flow.
            self.analyze_logical_binary_op(op, left, right)
        } else {
            let left_val = self.analyze_expr(left, UseKind::Borrow);
            let right_val = self.analyze_expr(right, UseKind::Borrow);

            self.insert_statement(MStatement {
                kind: MStatementKind::BinaryOp(MBinaryOp {
                    op: op.clone(),
                    left_operand: left_val,
                    right_operand: right_val,
                }),
            })
            .unwrap()
        }
    }

    /// Analyzes a logical binary operation. These need special handling because
    /// logical operations short-circuit, thereby affecting control flow.
    fn analyze_logical_binary_op(&mut self, op: &Operator, left: &AExpr, right: &AExpr) -> MValue {
        // Evaluate the left expression.
        let left_block_id = self.cur_block_id;
        let left_val = self.analyze_expr(left, UseKind::Borrow);
        let check_right_block_id = self.new_block();
        let result_block_id = self.new_block();

        // Set jump targets based on the type of logical operation.
        let branch_if = if op == &Operator::LogicalAnd {
            MBranchIf {
                condition: left_val,
                then_block_id: check_right_block_id,
                else_block_id: result_block_id,
            }
        } else {
            MBranchIf {
                condition: left_val,
                then_block_id: result_block_id,
                else_block_id: check_right_block_id,
            }
        };

        self.insert_statement(MStatement {
            kind: MStatementKind::BranchIf(branch_if),
        });

        // Evaluate the right expression and jump to the result block.
        self.switch_to_block(check_right_block_id);
        let right_block_id = self.cur_block_id;
        let right_val = self.analyze_expr(right, UseKind::Borrow);
        self.insert_statement(MStatement {
            kind: MStatementKind::Branch(MBranch {
                target_block_id: result_block_id,
            }),
        });

        // The end block computes the result as a phi node.
        self.switch_to_block(result_block_id);
        self.insert_statement(MStatement {
            kind: MStatementKind::Phi(MPhi {
                values: HashMap::from([(left_block_id, left_val), (right_block_id, right_val)]),
            }),
        })
        .unwrap()
    }

    /// Analyzes an expression. Expressions reduce to sets of SSA statements and
    /// may even affect control flow (like in the case of binary operations
    /// that can short-circuit).
    fn analyze_expr(&mut self, expr: &AExpr, use_kind: UseKind) -> MValue {
        if let Some(path) = self.try_get_move_path(expr) {
            // Check if we're using a value that was already moved.
            self.check_use(self.cur_block_id, path.as_str(), expr);

            // Only insert the move if the value is being moved.
            if use_kind == UseKind::Move {
                return self
                    .insert_statement(MStatement {
                        kind: MStatementKind::Move(MMove {
                            value_path: path,
                            start_pos: expr.start_pos().clone(),
                            end_pos: expr.end_pos().clone(),
                        }),
                    })
                    .unwrap();
            }
        }

        match &expr.kind {
            AExprKind::Symbol(symbol) => self.analyze_symbol(symbol, use_kind),

            AExprKind::MemberAccess(access) => self.analyze_member_access(access, use_kind),

            AExprKind::BoolLiteral(_)
            | AExprKind::I8Literal(_)
            | AExprKind::U8Literal(_)
            | AExprKind::I32Literal(_)
            | AExprKind::U32Literal(_)
            | AExprKind::F32Literal(_)
            | AExprKind::I64Literal(_)
            | AExprKind::U64Literal(_)
            | AExprKind::F64Literal(_, _)
            | AExprKind::IntLiteral(_, _)
            | AExprKind::UintLiteral(_)
            | AExprKind::StrLiteral(_)
            | AExprKind::Sizeof(_) => MValue::new_immediate(),

            AExprKind::StructInit(struct_init) => self.analyze_struct_init(struct_init),

            AExprKind::EnumInit(enum_init) => self.analyze_enum_init(enum_init),

            AExprKind::TupleInit(tuple_init) => self.analyze_tuple_init(tuple_init),

            AExprKind::ArrayInit(array_init) => self.analyze_array_init(array_init),

            AExprKind::Index(index) => self.analyze_index(index, use_kind),

            AExprKind::FunctionCall(call) => self.analyze_fn_call(call).unwrap(),

            AExprKind::UnaryOperation(op, operand) => self.analyze_unary_op(op, operand, use_kind),

            AExprKind::BinaryOperation(left, op, right) => self.analyze_binary_op(op, left, right),

            AExprKind::TypeCast(operand, _) => self.analyze_expr(operand, use_kind),

            AExprKind::AnonFunction(func) => self.analyze_anon_fn(func),

            AExprKind::Unknown => unreachable!(),
        }
    }

    /// Analyzes a variable assignment.
    fn analyze_var_assign(&mut self, var_assign: &AVarAssign) {
        let value = self.analyze_expr(&var_assign.val, UseKind::Move);

        if let Some(target) = self.try_get_move_path(&var_assign.target) {
            self.insert_statement(MStatement {
                kind: MStatementKind::Assign(MAssign { target, value }),
            });
        } else {
            let target = self.analyze_expr(&var_assign.target, UseKind::Borrow);
            self.insert_statement(MStatement {
                kind: MStatementKind::Store(MStore { target, value }),
            });
        }
    }

    /// Analyzes a constant declaration.
    fn analyze_const_decl(&mut self, const_decl: &AConst) {
        self.insert_statement(MStatement {
            kind: MStatementKind::Declare(MDeclare {
                var_name: const_decl.name.clone(),
                value: MValue::new_immediate(),
            }),
        });
    }

    /// Analyzes a closure.
    fn analyze_closure(&mut self, closure: &AClosure) {
        self.stack.push(MScope::new());
        self.analyze_statements(&closure.statements);
        self.stack.pop();
    }

    /// Tries to extract the path to a moved value in `expr`. Returns `None` if
    /// `expr` doesn't represent a moved value.
    fn try_get_move_path(&mut self, expr: &AExpr) -> Option<String> {
        if !self.ctx.must_get_type(expr.type_key).requires_move()
            || expr.kind.is_const()
            || expr.kind.is_type()
        {
            return None;
        }

        match &expr.kind {
            AExprKind::Symbol(symbol) => Some(symbol.name.clone()),

            AExprKind::MemberAccess(access) => {
                if access.base_expr.kind.is_const() {
                    return None;
                }

                if let Some(path) = self.try_get_move_path(&access.base_expr) {
                    return Some(format!("{path}.{}", access.member_name));
                }

                None
            }

            AExprKind::Index(index) if !index.collection_expr.kind.is_const() => {
                if let Some(path) = self.try_get_move_path(&index.collection_expr) {
                    if let Some(i) = index.index_expr.try_into_const_uint(self.ctx) {
                        return Some(format!("{path}.({i})"));
                    }

                    return Some(path);
                }

                None
            }

            _ => None,
        }
    }

    /// Checks `value_path` to see if it is using a value that was already moved.
    fn check_use<T: Locatable>(&mut self, start_block_id: usize, value_path: &str, loc: &T) {
        let mut blocks_tracked = HashSet::from([start_block_id]);
        let mut blocks_to_search = VecDeque::from([start_block_id]);

        'next_block: while let Some(block_id) = blocks_to_search.pop_front() {
            let block = self.get_block(block_id);

            for statement in block.statements.iter().rev() {
                match &statement.kind {
                    // Check if the move conflicts.
                    MStatementKind::Move(mv)
                        if moves_conflict(mv.value_path.as_str(), value_path) =>
                    {
                        self.ctx.insert_err(
                            AnalyzeError::new(
                                ErrorKind::UseOfMovedValue,
                                format_code!(
                                    "cannot use {} because it was already moved",
                                    value_path
                                )
                                .as_str(),
                                loc,
                            )
                            .with_detail(
                                format!(
                                    "The conflicting move of {} occurs at {}.",
                                    format_code!(mv.value_path),
                                    mv.start_pos(),
                                )
                                .as_str(),
                            )
                            .with_help(
                                format!(
                                    "Consider copying or borrowing {} at {} instead \
                                of moving it.",
                                    format_code!(mv.value_path),
                                    mv.start_pos(),
                                )
                                .as_str(),
                            ),
                        );
                        return;
                    }

                    // Check if this is where the variable was declared. If so,
                    // we know we're done searching this block.
                    MStatementKind::Declare(MDeclare { var_name, .. })
                        if move_is_from_var(var_name, value_path) =>
                    {
                        continue 'next_block;
                    }

                    // Check if this is where the variable was assigned. If so,
                    // we know we're done searching this block.
                    MStatementKind::Assign(assign)
                        if moves_conflict(assign.target.as_str(), value_path) =>
                    {
                        continue 'next_block;
                    }

                    _ => {}
                }
            }

            // We didn't find any conflicting moves or the variable declaration
            // on this block, so check predecessors.
            for pred_block_id in &block.predecessor_block_ids {
                if !blocks_tracked.contains(pred_block_id) {
                    blocks_to_search.push_back(*pred_block_id);
                    blocks_tracked.insert(*pred_block_id);
                }
            }
        }
    }

    /// Tries to find a cycle starting at the first block in the given path.
    /// Returns the sequence of block IDs on the cyclical path if one is found.
    fn find_cycle(&self, mut current_path: Vec<usize>) -> Option<Vec<usize>> {
        let target_block_id = *current_path.first().unwrap();
        let cur_block_id = *current_path.last().unwrap();
        let next_block_ids = self.get_descendant_block_ids(cur_block_id);

        for block_id in next_block_ids {
            if block_id == target_block_id {
                return Some(current_path);
            } else if current_path.contains(&block_id) {
                // We've found a cycle, but it's not the one we're looking for.
                continue;
            }

            current_path.push(block_id);

            if let Some(path) = self.find_cycle(current_path.clone()) {
                return Some(path);
            }

            current_path.pop();
        }

        None
    }

    /// Returns the IDs of the given block's descendents.
    fn get_descendant_block_ids(&self, block_id: usize) -> Vec<usize> {
        let last_statement = match self.get_block(block_id).statements.last() {
            Some(statement) => statement,
            None => panic!("block {block_id} has no statements"),
        };

        match &last_statement.kind {
            MStatementKind::Branch(branch) => {
                vec![branch.target_block_id]
            }

            MStatementKind::BranchIf(branch_if) => {
                vec![branch_if.then_block_id, branch_if.else_block_id]
            }

            MStatementKind::Return(_) => vec![],

            _ => panic!("block {block_id} has no descendants"),
        }
    }
}

fn get_root_var_name(path: &str) -> &str {
    get_move_parts(path).first().unwrap()
}

fn moves_conflict(a: &str, b: &str) -> bool {
    let a_parts = get_move_parts(a);
    let b_parts = get_move_parts(b);

    a_parts.starts_with(&b_parts) || b_parts.starts_with(&a_parts)
}

fn get_move_parts(move_path: &str) -> Vec<&str> {
    move_path.split(".").collect()
}

fn move_is_from_var(var_name: &str, move_path: &str) -> bool {
    get_root_var_name(move_path) == var_name
}

/// Performs control flow analysis on each function defined in the module.
/// Analysis includes checking for use-after-move violations and dead code.
pub fn analyze_module_fns(ctx: &mut ProgramContext, module: &AModule) {
    for statement in &module.statements {
        if let AStatement::FunctionDeclaration(func) = statement {
            CFGAnalyzer::analyze_fn(ctx, func);
        }
    }
}
