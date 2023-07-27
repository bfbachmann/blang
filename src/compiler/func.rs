use std::collections::HashMap;

use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::values::{
    BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue,
};
use inkwell::IntPredicate;

use crate::analyzer::closure::RichClosure;
use crate::analyzer::cond::RichCond;
use crate::analyzer::expr::{RichExpr, RichExprKind};
use crate::analyzer::func::{RichFn, RichFnCall, RichRet};
use crate::analyzer::statement::RichStatement;
use crate::compiler::context::{
    BranchContext, CompilationContext, FnContext, LoopContext, StatementContext,
};
use crate::compiler::convert;
use crate::compiler::error::{CompileError, CompileResult, ErrorKind};
use crate::parser::op::Operator;
use crate::parser::r#type::Type;

/// Compiles type-rich (i.e. semantically valid) functions.
pub struct FnCompiler<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    module: &'a Module<'ctx>,

    vars: HashMap<String, PointerValue<'ctx>>,
    fn_value: Option<FunctionValue<'ctx>>,
    stack: Vec<CompilationContext<'ctx>>,
    cur_block: Option<BasicBlock<'ctx>>,
}

impl<'a, 'ctx> FnCompiler<'a, 'ctx> {
    /// Compiles the given function.
    pub fn compile(
        context: &'ctx Context,
        builder: &'a Builder<'ctx>,
        fpm: &'a PassManager<FunctionValue<'ctx>>,
        module: &'a Module<'ctx>,
        func: &RichFn,
    ) -> CompileResult<FunctionValue<'ctx>> {
        let mut fn_compiler = FnCompiler {
            context,
            builder,
            fpm,
            module,
            vars: HashMap::new(),
            fn_value: None,
            stack: vec![],
            cur_block: None,
        };

        fn_compiler.compile_fn(func)
    }

    /// Creates a new basic block for this function and returns it.
    fn append_block(&mut self, name: &str) -> BasicBlock<'ctx> {
        let block = self
            .context
            .append_basic_block(self.fn_value.unwrap(), name);
        self.cur_block = Some(block);
        block
    }

    /// Creates a new statement context and pushes it onto the stack.
    fn push_statement_ctx(&mut self) {
        self.stack
            .push(CompilationContext::Statement(StatementContext::new()));
    }

    /// Creates a new branch context and pushes it onto the stack.
    fn push_branch_ctx(&mut self) {
        self.stack
            .push(CompilationContext::Branch(BranchContext::new()));
    }

    /// Creates a new loop context and pushes it onto the stack.
    fn push_loop_ctx(&mut self) {
        let begin_block = self.append_block("loop_begin");
        let loop_ctx = LoopContext::new(begin_block);
        self.stack.push(CompilationContext::Loop(loop_ctx));
    }

    /// Creates a new function context and pushes it onto the stack.
    fn push_fn_ctx(&mut self) {
        self.stack.push(CompilationContext::Func(FnContext::new()));
    }

    /// Pops the current loop context from the stack. Panics if the current context is not a loop
    /// context.
    fn pop_ctx(&mut self) -> CompilationContext<'ctx> {
        self.stack.pop().unwrap()
    }

    /// Returns true if we are currently inside a loop.
    fn is_in_loop(&self) -> bool {
        for ctx in self.stack.iter().rev() {
            if let CompilationContext::Loop(_) = ctx {
                return true;
            }
        }

        false
    }

    /// Sets the `guarantees_return` flag on the current context.
    fn set_guarantees_return(&mut self, guarantees_return: bool) {
        match self.stack.last_mut().unwrap() {
            CompilationContext::Loop(ctx) => {
                ctx.guarantees_return = guarantees_return;
                ctx.guarantees_terminator = guarantees_return || ctx.guarantees_terminator;
            }
            CompilationContext::Func(ctx) => {
                ctx.guarantees_return = guarantees_return;
            }
            CompilationContext::Statement(ctx) => {
                ctx.guarantees_return = guarantees_return;
                ctx.guarantees_terminator = guarantees_return || ctx.guarantees_terminator;
            }
            CompilationContext::Branch(ctx) => {
                ctx.guarantees_return = guarantees_return;
                ctx.guarantees_terminator = guarantees_return || ctx.guarantees_terminator;
            }
        }
    }

    /// Sets the `guarantees_terminator` flag on the current context, if applicable.
    fn set_guarantees_terminator(&mut self, guarantees_term: bool) {
        match self.stack.last_mut().unwrap() {
            CompilationContext::Statement(ctx) => {
                ctx.guarantees_terminator = guarantees_term;
            }
            CompilationContext::Branch(ctx) => {
                ctx.guarantees_terminator = guarantees_term;
            }
            CompilationContext::Loop(ctx) => {
                ctx.guarantees_terminator = guarantees_term;
            }
            CompilationContext::Func(_) => {}
        }
    }

    /// Returns a reference to the nearest loop context in the stack.
    fn get_loop_ctx(&mut self) -> &mut LoopContext<'ctx> {
        for ctx in self.stack.iter_mut().rev() {
            if let CompilationContext::Loop(loop_ctx) = ctx {
                return loop_ctx;
            }
        }

        panic!("call to get_loop_ctx occurred outside of loop");
    }

    /// Returns the existing loop end block from the current loop context, if one exists. Otherwise,
    /// creates one, adds it to the current loop context, and returns it. Panics if there is no
    /// loop context in the stack.
    fn get_or_create_loop_end_block(&mut self) -> BasicBlock<'ctx> {
        if let Some(end_block) = self.get_loop_end_block() {
            return end_block;
        }

        let end_block = self.append_block("loop_end");

        let ctx = self.get_loop_ctx();
        ctx.end_block = Some(end_block);
        ctx.end_block.unwrap()
    }

    /// Fetches the loop end block from the current loop context. Panics if there is no loop
    /// context (i.e. if not called from within a loop).
    fn get_loop_end_block(&mut self) -> Option<BasicBlock<'ctx>> {
        let loop_ctx = self.get_loop_ctx();
        loop_ctx.end_block
    }

    /// Returns the block that begins the current loop. Panics if there is no loop context (i.e. if
    /// not called from within a loop).
    fn get_loop_begin_block(&mut self) -> BasicBlock<'ctx> {
        let loop_ctx = self.get_loop_ctx();
        loop_ctx.begin_block
    }

    /// If inside a loop, sets the loop's `contains_return` flag.
    fn set_loop_contains_return(&mut self, contains_return: bool) {
        if self.is_in_loop() {
            let loop_ctx = self.get_loop_ctx();
            loop_ctx.contains_return = contains_return;
        }
    }

    /// Compiles the given function.
    fn compile_fn(&mut self, func: &RichFn) -> CompileResult<FunctionValue<'ctx>> {
        // Retrieve the function and create a new "entry" block at the start of the function
        // body.
        let fn_val = self
            .module
            .get_function(func.signature.name.as_str())
            .unwrap();
        self.fn_value = Some(fn_val);

        let entry = self.append_block("entry");

        // Start building from the beginning of the entry block.
        self.builder.position_at_end(entry);

        // Define function arguments as variables on the stack so they can be referenced in blocks.
        for (arg_val, arg) in fn_val.get_param_iter().zip(func.signature.args.iter()) {
            self.create_var(arg.name.as_str(), &arg.typ, arg_val);
        }

        // Push a function context onto the stack so we can reference it later.
        self.push_fn_ctx();

        // Compile the function body. This will return true if the function already ends in an
        // explicit return statement (or a set of unconditional branches that all return).
        self.compile_closure(&func.body)?;

        // If the function body does not end in an explicit return (or other terminator
        // instruction), we have to insert one.
        let ctx = self.pop_ctx().to_fn();
        if !ctx.guarantees_return {
            self.builder.build_return(None);
        }

        // Verify and optimize the function.
        if fn_val.verify(true) {
            self.fpm.run_on(&fn_val);
            Ok(fn_val)
        } else {
            fn_val.print_to_stderr();
            unsafe {
                fn_val.delete();
            }

            Err(CompileError::new(
                ErrorKind::FnVerificationFailed,
                format!("failed to verify function {}", func.signature).as_str(),
            ))
        }
    }

    /// Creates and initializes a new variable with the given name, type, and initial value.
    /// Panics if a variable by the same name already exists.
    fn create_var(&mut self, name: &str, typ: &Type, val: BasicValueEnum<'ctx>) {
        let ptr = self.create_entry_alloc(name, typ, val);
        self.builder.build_store(ptr, val);
        assert!(self.vars.insert(name.to_string(), ptr).is_none());
    }

    /// Assigns the value to the variable with the given name. Panics if no such variable exists.
    fn assign_var(&mut self, name: &str, val: BasicValueEnum) {
        let var = self.vars.get(name).unwrap();
        self.builder.build_store(*var, val);
    }

    /// Gets the value of the variable with the given name. Panics if no such variable exists.
    fn get_var(&self, name: &str) -> BasicValueEnum<'ctx> {
        let var = self.vars.get(name).unwrap();
        let val = self.builder.build_load(var.get_type(), *var, name);
        val
    }

    /// Creates a new stack allocation instruction in the entry block of the current function.
    fn create_entry_alloc(
        &self,
        name: &str,
        typ: &Type,
        val: BasicValueEnum<'ctx>,
    ) -> PointerValue<'ctx> {
        let entry = self.fn_value.unwrap().get_first_basic_block().unwrap();

        // Switch to the beginning of the entry block if we're not already there.
        match entry.get_first_instruction() {
            Some(first_instr) => self.builder.position_before(&first_instr),
            None => self.builder.position_at_end(entry),
        }

        let val = if *typ == Type::String {
            self.builder.build_alloca(val.get_type(), name)
        } else {
            self.builder
                .build_alloca(convert::to_basic_type(self.context, typ), name)
        };

        // Make sure we continue from where we left off as our builder position may have changed
        // in this function.
        self.builder.position_at_end(self.cur_block.unwrap());

        val
    }

    /// Compiles all statements in the closure.
    fn compile_closure(&mut self, closure: &RichClosure) -> CompileResult<()> {
        for (i, statement) in closure.statements.iter().enumerate() {
            // Create a new statement context that can store information about the statement
            // we're about to compile.
            self.push_statement_ctx();

            self.compile_statement(statement)?;

            // Pop the statement context now that we've compiled the statement.
            let ctx = self.pop_ctx().to_statement();

            // If this is the last statement in the closure, we need to propagate information about
            // terminators and returns to the parent context.
            if i + 1 == closure.statements.len() {
                self.set_guarantees_return(ctx.guarantees_return);
                self.set_guarantees_terminator(ctx.guarantees_terminator);
            }
        }

        Ok(())
    }

    /// Compiles a statement.
    fn compile_statement(&mut self, statement: &RichStatement) -> CompileResult<()> {
        match statement {
            RichStatement::VariableDeclaration(decl) => {
                // Get the value of the expression being assigned to the variable.
                let val = self.compile_expr(&decl.val);

                // Create and initialize the variable.
                self.create_var(decl.name.as_str(), &decl.typ, val);
            }
            RichStatement::VariableAssignment(assign) => {
                let val = self.compile_expr(&assign.val);
                self.assign_var(assign.name.as_str(), val);
            }
            RichStatement::FunctionDeclaration(func) => {
                self.compile_fn(func)?;
            }
            RichStatement::Closure(closure) => {
                self.compile_closure(closure)?;
            }
            RichStatement::FunctionCall(call) => {
                self.compile_call(call);
            }
            RichStatement::Conditional(cond) => {
                self.compile_cond(cond)?;
            }
            RichStatement::Loop(closure) => {
                self.compile_loop(closure)?;
            }
            RichStatement::Break => {
                self.compile_break();
            }
            RichStatement::Continue => {
                self.compile_continue();
            }
            RichStatement::Return(ret) => {
                self.compile_return(ret);
            }
        };

        Ok(())
    }

    /// Compiles a break statement.
    fn compile_break(&mut self) {
        self.set_guarantees_terminator(true);
        let loop_end = self.get_or_create_loop_end_block();
        self.builder.build_unconditional_branch(loop_end);
    }

    /// Compiles a continue statement.
    fn compile_continue(&mut self) {
        self.set_guarantees_terminator(true);
        let loop_begin = self.get_loop_begin_block();
        self.builder.build_unconditional_branch(loop_begin);
    }

    /// Compiles a loop.
    fn compile_loop(&mut self, loop_body: &RichClosure) -> CompileResult<()> {
        // Create a loop context to store information about the loop body.
        self.push_loop_ctx();

        // Create a new block for the loop body, and branch to it.
        let begin_block = self.get_loop_ctx().begin_block;
        self.builder.build_unconditional_branch(begin_block);
        self.builder.position_at_end(begin_block);

        // Compile the loop body.
        self.compile_closure(loop_body)?;

        // Pop the loop context now that we've compiled the loop body.
        let ctx = self.pop_ctx().to_loop();

        // If the loop doesn't already end in a terminator instruction, we need to branch back
        // to the beginning of the loop.
        if !ctx.guarantees_terminator {
            self.builder.build_unconditional_branch(begin_block);
        }

        // Update the parent context with return information.
        self.set_guarantees_return(ctx.guarantees_return);

        // If there is a loop end block, it means the loop has a break and we need to continue
        // compilation on the loop end block. In this case, we also inform the parent context
        // that this loop is not guaranteed to end in a terminator or return (since it can be broken
        // out of).
        if let Some(end_block) = ctx.end_block {
            self.builder.position_at_end(end_block);
            self.set_guarantees_terminator(false);
            self.set_guarantees_return(false);
        } else {
            // The loop has no break statements.
            self.set_guarantees_terminator(true);

            // If there is a return inside the loop and it never breaks, we can tell the
            // parent context that is is guaranteed to return (or run forever, which is fine).
            self.set_guarantees_return(ctx.contains_return);
        }

        Ok(())
    }

    /// Compiles a conditional.
    fn compile_cond(&mut self, cond: &RichCond) -> CompileResult<()> {
        // Compile each branch, recording whether it returns.
        let mut end_block = None;
        let mut all_branches_return = true;
        let mut all_branches_terminate = true;
        let mut else_branch_exists = false;
        for (i, branch) in cond.branches.iter().enumerate() {
            // If there is a branch condition, it means we are on an "if" or "else if" branch.
            // Otherwise, it means we're on an "else" branch.
            if let Some(expr) = &branch.cond {
                // Create a "then" block to jump to if the branch condition is true.
                let then_block = self.append_block("cond_branch");

                // Create an "else" block to jump to if the branch condition is false. If this is
                // the last branch in the conditional, the "else" block is the "end" block.
                // Otherwise, we create a new "else" block.
                let else_block = if i + 1 == cond.branches.len() {
                    if end_block.is_none() {
                        end_block = Some(self.append_block("cond_end"));
                    }

                    end_block.unwrap()
                } else {
                    self.append_block("cond_branch")
                };

                // Branch from the current block based on the value of the conditional expression.
                let cond_val = self.get_bool(self.compile_expr(expr));
                self.builder
                    .build_conditional_branch(cond_val, then_block, else_block);

                // Fill the "then" block with the branch body.
                self.builder.position_at_end(then_block);

                // Create a branch context to store information about the branch being compiled.
                self.push_branch_ctx();

                // Compile the branch body.
                self.compile_closure(&branch.body)?;

                // Pop the branch context now that we're done compiling the branch.
                let ctx = self.pop_ctx().to_branch();

                all_branches_return = all_branches_return && ctx.guarantees_return;
                all_branches_terminate = all_branches_terminate && ctx.guarantees_terminator;

                // If this branch does not end in an unconditional return, we need to complete
                // the corresponding "then" block with an unconditional jump to the "end" block.
                if !ctx.guarantees_terminator {
                    if end_block.is_none() {
                        end_block = Some(self.append_block("cond_end"));
                    }
                    self.builder.build_unconditional_branch(end_block.unwrap());
                }

                // Continue on the "else" block.
                self.builder.position_at_end(else_block);
            } else {
                // This is an else branch, so we must execute the branch body.
                else_branch_exists = true;
                self.push_branch_ctx();
                self.compile_closure(&branch.body)?;
                let ctx = self.pop_ctx().to_branch();
                all_branches_return = all_branches_return && ctx.guarantees_return;
                all_branches_terminate = all_branches_terminate && ctx.guarantees_terminator;

                // If this branch does not end in an unconditional return, we need to complete
                // the current block with an unconditional jump to the "end" block.
                if !ctx.guarantees_terminator {
                    if end_block.is_none() {
                        end_block = Some(self.append_block("cond_end"));
                    }
                    self.builder.build_unconditional_branch(end_block.unwrap());
                }
            }
        }

        // If there is an "end" block, continue on that block.
        if let Some(block) = end_block {
            self.builder.position_at_end(block);
        }

        // Update the parent context with return and terminator information.
        self.set_guarantees_return(all_branches_return && else_branch_exists);
        self.set_guarantees_terminator(all_branches_terminate && else_branch_exists);
        Ok(())
    }

    /// Compiles a return statement.
    fn compile_return(&mut self, ret: &RichRet) {
        self.set_guarantees_return(true);
        self.set_loop_contains_return(true);

        match &ret.val {
            Some(expr) => {
                let result = self.compile_expr(expr);
                self.builder.build_return(Some(&result));
            }
            None => {
                self.builder.build_return(None);
            }
        }
    }

    /// Compiles an arbitrary expression.
    fn compile_expr(&self, expr: &RichExpr) -> BasicValueEnum<'ctx> {
        let result = match &expr.kind {
            RichExprKind::VariableReference(name) => self.get_var(name),

            RichExprKind::BoolLiteral(b) => self
                .context
                .bool_type()
                .const_int(*b as u64, false)
                .as_basic_value_enum(),

            RichExprKind::I64Literal(i) => self
                .context
                .i64_type()
                .const_int(i.abs() as u64, *i < 0)
                .as_basic_value_enum(),

            RichExprKind::StringLiteral(literal) => {
                let char_type = self.context.i32_type();

                // Check if this string literal already exists as a global.
                let global = if let Some(global) = self.module.get_global(literal) {
                    global
                } else {
                    let mut chars: Vec<u32> = literal.clone().chars().map(|c| c as u32).collect();
                    chars.push(0);

                    let array_type = char_type.array_type((chars.len()) as u32);
                    let array_vals: Vec<_> = chars
                        .iter()
                        .map(|v| char_type.const_int((*v).into(), false))
                        .collect();

                    let global = self.module.add_global(array_type, None, literal.as_str());
                    global.set_initializer(&char_type.const_array(array_vals.as_slice()));

                    global
                };

                self.builder.build_bitcast(
                    global.as_pointer_value(),
                    convert::to_basic_type(self.context, &Type::String),
                    "str_lit_as_i32_ptr",
                )
            }

            RichExprKind::FunctionCall(call) => self.compile_call(call).unwrap(),

            // TODO
            // RichExprKind::AnonFunction(Box<RichFn>),
            RichExprKind::UnaryOperation(op, expr) => self.compile_unary_op(op, expr),

            RichExprKind::BinaryOperation(left_expr, op, right_expr) => {
                self.compile_bin_op(left_expr, op, right_expr)
            }

            other => {
                panic!("{other} not implemented");
            }
        };

        // Dereference the result if it's a pointer.
        self.deref_if_ptr(result, &expr.typ)
    }

    /// Compiles a function call, returning the result if one exists.
    fn compile_call(&self, call: &RichFnCall) -> Option<BasicValueEnum<'ctx>> {
        // Get the function value from the module.
        let func = self.module.get_function(call.fn_name.as_str()).unwrap();

        // Compile call args.
        let mut args: Vec<BasicMetadataValueEnum> = vec![];
        for arg in &call.args {
            // Compile the argument expression, making sure to dereference any pointers
            // if necessary.
            let arg_val = self.compile_expr(arg);
            args.push(arg_val.into());
        }

        // Compile the function call and return the result.
        self.builder
            .build_call(func, args.as_slice(), call.fn_name.as_str())
            .try_as_basic_value()
            .left()
    }

    /// Compiles a unary operation expression.
    fn compile_unary_op(&self, op: &Operator, expr: &RichExpr) -> BasicValueEnum<'ctx> {
        // Only the not operator is supported as a unary operator at the moment.
        if *op != Operator::Not {
            panic!("unsupported unary operator {op}");
        }

        // Compile the operand expression.
        let expr_val = self.compile_expr(expr);

        // If the value is a pointer (i.e. a variable reference), we need to get the bool
        // value it points to.
        let operand = if expr_val.is_pointer_value() {
            self.builder.build_ptr_to_int(
                expr_val.into_pointer_value(),
                self.context.bool_type(),
                "negated_bool",
            )
        } else {
            expr_val.into_int_value()
        };

        // Build the logical not as the result of the int compare != 0.
        let result = self.builder.build_int_compare(
            IntPredicate::NE,
            operand,
            self.context.bool_type().const_int(0, false),
            "not_zero",
        );

        result
            .const_cast(self.context.bool_type(), false)
            .as_basic_value_enum()
    }

    /// Compiles a binary operation expression.
    fn compile_bin_op(
        &self,
        left_expr: &RichExpr,
        op: &Operator,
        right_expr: &RichExpr,
    ) -> BasicValueEnum<'ctx> {
        let lhs = self.compile_expr(left_expr);
        let rhs = self.compile_expr(right_expr);

        if op.is_arithmetic() {
            self.compile_arith_op(lhs, op, rhs).as_basic_value_enum()
        } else if op.is_comparator() {
            self.compile_cmp(lhs, op, rhs).as_basic_value_enum()
        } else if op.is_logical() {
            self.compile_logical_op(lhs, op, rhs).as_basic_value_enum()
        } else {
            panic!("unsupported operator {op}")
        }
    }

    /// Compiles a logical (boolean) operation expression.
    fn compile_logical_op(
        &self,
        lhs: BasicValueEnum<'ctx>,
        op: &Operator,
        rhs: BasicValueEnum<'ctx>,
    ) -> IntValue<'ctx> {
        // Expect both operands to be of type bool.
        let lhs = self.get_bool(lhs);
        let rhs = self.get_bool(rhs);

        match op {
            Operator::LogicalAnd => self.builder.build_and(lhs, rhs, "logical_and"),
            Operator::LogicalOr => self.builder.build_or(lhs, rhs, "logical_or"),
            other => panic!("unexpected logical operator {other}"),
        }
    }

    /// Compiles a comparison operation expression.
    fn compile_cmp(
        &self,
        lhs: BasicValueEnum<'ctx>,
        op: &Operator,
        rhs: BasicValueEnum<'ctx>,
    ) -> IntValue<'ctx> {
        // TODO: will it work if we always treat operands as ints?
        let lhs = self.get_int(lhs);
        let rhs = self.get_int(rhs);

        match op {
            Operator::EqualTo => self
                .builder
                .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq"),
            Operator::NotEqualTo => {
                self.builder
                    .build_int_compare(IntPredicate::NE, lhs, rhs, "ne")
            }
            Operator::GreaterThan => {
                self.builder
                    .build_int_compare(IntPredicate::SGT, lhs, rhs, "gt")
            }
            Operator::LessThan => self
                .builder
                .build_int_compare(IntPredicate::SLT, lhs, rhs, "lt"),
            Operator::GreaterThanOrEqual => {
                self.builder
                    .build_int_compare(IntPredicate::SGE, lhs, rhs, "ge")
            }
            Operator::LessThanOrEqual => {
                self.builder
                    .build_int_compare(IntPredicate::SLE, lhs, rhs, "le")
            }
            other => panic!("unexpected comparison operator {other}"),
        }
    }

    /// Compiles a binary arithmetic operation expression.
    fn compile_arith_op(
        &self,
        lhs: BasicValueEnum<'ctx>,
        op: &Operator,
        rhs: BasicValueEnum<'ctx>,
    ) -> IntValue<'ctx> {
        // Expect both operands to be of type i64.
        let lhs = self.get_int(lhs);
        let rhs = self.get_int(rhs);

        match op {
            Operator::Add => self.builder.build_int_add(lhs, rhs, "sum"),
            Operator::Subtract => self.builder.build_int_sub(lhs, rhs, "diff"),
            Operator::Multiply => self.builder.build_int_mul(lhs, rhs, "prod"),
            Operator::Divide => self.builder.build_int_signed_div(lhs, rhs, "quot"),
            Operator::Modulo => self.builder.build_int_signed_rem(lhs, rhs, "rem"),
            other => panic!("unexpected arithmetic operator {other}"),
        }
    }

    /// Returns the given value as a boolean int value. This is useful for cases where the value may
    /// be a pointer to a bool.
    fn get_bool(&self, val: BasicValueEnum<'ctx>) -> IntValue<'ctx> {
        if val.is_pointer_value() {
            self.builder.build_ptr_to_int(
                val.into_pointer_value(),
                self.context.bool_type(),
                "ptr_to_bool",
            )
        } else {
            val.into_int_value()
        }
    }

    /// Returns the given value as an int value. This is useful for cases where the value may be
    /// a pointer to an int.
    fn get_int(&self, val: BasicValueEnum<'ctx>) -> IntValue<'ctx> {
        if val.is_pointer_value() {
            self.builder.build_ptr_to_int(
                val.into_pointer_value(),
                self.context.i64_type(),
                "ptr_to_int",
            )
        } else {
            val.into_int_value()
        }
    }

    /// If the given value is a pointer, it will be dereferenced as the given type. Otherwise
    /// the value is simply returned.
    fn deref_if_ptr(&self, val: BasicValueEnum<'ctx>, typ: &Type) -> BasicValueEnum<'ctx> {
        match typ {
            Type::I64 => self.get_int(val).as_basic_value_enum(),
            Type::Bool => self.get_bool(val).as_basic_value_enum(),
            Type::String => val, // TODO: probably not safe. Maybe this should be a bitcast.
            other => panic!("cannot dereference pointer to value of type {other}"),
        }
    }
}
