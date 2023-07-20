use std::collections::HashMap;

use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::{AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum};
use inkwell::values::{
    BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue,
};
use inkwell::IntPredicate;

use crate::analyzer::closure::RichClosure;
use crate::analyzer::cond::RichCond;
use crate::analyzer::expr::{RichExpr, RichExprKind};
use crate::analyzer::func::{RichFn, RichFnCall, RichRet};
use crate::analyzer::statement::RichStatement;
use crate::compiler::error::{CompileError, CompileResult, ErrorKind};
use crate::parser::op::Operator;
use crate::parser::r#type::Type;

/// Stores information about the current loop being compiled.
struct LoopContext<'ctx> {
    end_block: Option<BasicBlock<'ctx>>,
    has_return: bool,
}

/// Compiles type-rich (i.e. semantically valid) functions.
pub struct FnCompiler<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    module: &'a Module<'ctx>,

    vars: HashMap<String, PointerValue<'ctx>>,
    fn_value: Option<FunctionValue<'ctx>>,
    loop_ctx: Vec<LoopContext<'ctx>>,
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
            loop_ctx: vec![],
        };

        fn_compiler.compile_fn(func)
    }

    /// Creates a new loop context, adds it to the stack, and returns it.
    fn new_loop_ctx(&mut self) -> BasicBlock<'ctx> {
        let loop_begin = self
            .context
            .append_basic_block(self.fn_value.unwrap(), "loopbegin");
        self.loop_ctx.push(LoopContext {
            end_block: None,
            has_return: false,
        });
        loop_begin
    }

    /// Pops the current loop context from the stack. This panics if there is no current loop
    /// context.
    fn pop_loop_ctx(&mut self) {
        self.loop_ctx.pop().unwrap();
    }

    /// Returns true if we are currently inside a loop.
    fn is_in_loop(&self) -> bool {
        !self.loop_ctx.is_empty()
    }

    /// Marks the current loop at the top of the stack as containing a return.
    fn set_loop_has_return(&mut self) {
        self.loop_ctx.last_mut().unwrap().has_return = true;
    }

    /// Returns true if the current loop at the top of the stack contains a return statement.
    fn loop_has_return(&self) -> bool {
        self.loop_ctx.last().unwrap().has_return
    }

    /// Returns the existing loop end block from the current loop context, if one exists. Otherwise,
    /// creates one, adds it to the current loop context, and returns it.
    fn get_or_create_loop_end_block(&mut self) -> BasicBlock<'ctx> {
        let loop_block = self.loop_ctx.last_mut().unwrap();

        if let Some(end_block) = loop_block.end_block {
            return end_block;
        }

        let end_block = self
            .context
            .append_basic_block(self.fn_value.unwrap(), "loopend");
        loop_block.end_block = Some(end_block);
        end_block
    }

    /// Fetches the loop end block from the current loop context. Panics if there is no loop
    /// context.
    fn get_loop_end_block(&self) -> Option<BasicBlock<'ctx>> {
        self.loop_ctx.last().unwrap().end_block
    }

    /// Compiles the given function.
    fn compile_fn(&mut self, func: &RichFn) -> CompileResult<FunctionValue<'ctx>> {
        // Retrieve the function and create a new "entry" block at the start of the function
        // body.
        let fn_val = self
            .module
            .get_function(func.signature.name.as_str())
            .unwrap();
        let entry = self.context.append_basic_block(fn_val, "entry");

        // Start building from the beginning of the entry block.
        self.builder.position_at_end(entry);

        // Track the function value so we can reference it later (when we need to allocate variables
        // in its entry block.
        self.fn_value = Some(fn_val);

        // Define function arguments as variables on the stack so they can be referenced in blocks.
        for (arg_val, arg) in fn_val.get_param_iter().zip(func.signature.args.iter()) {
            self.create_var(arg.name.as_str(), &arg.typ, arg_val);
        }

        // Compile the function body. This will return true if the function already ends in an
        // explicit return statement (or a set of unconditional branches that all return).
        let returns = self.compile_closure(&func.body)?;

        // If the function body does not end in an explicit return, we have to insert one.
        if !returns {
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
    fn create_var(&mut self, name: &str, typ: &Type, val: BasicValueEnum) {
        let ptr = self.create_entry_alloc(name, typ);
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
    fn create_entry_alloc(&self, name: &str, typ: &Type) -> PointerValue<'ctx> {
        let builder = self.context.create_builder();
        let entry = self.fn_value.unwrap().get_first_basic_block().unwrap();

        match entry.get_first_instruction() {
            Some(first_instr) => builder.position_before(&first_instr),
            None => builder.position_at_end(entry),
        }

        builder.build_alloca(get_basic_type(self.context, typ), name)
    }

    /// Compiles all statements in the closure. Returns true if the closure returns unconditionally.
    fn compile_closure(&mut self, closure: &RichClosure) -> CompileResult<bool> {
        for (i, statement) in closure.statements.iter().enumerate() {
            let returned = self.compile_statement(statement)?;
            let is_last = i == closure.statements.len() - 1;
            if is_last {
                return Ok(returned);
            }
        }

        Ok(false)
    }

    /// Compiles a statement and returns true if the statement always results in a return.
    /// Statements that would always result in a return are
    ///  - explicit return statements
    ///  - conditionals where every possible branch results in a return
    ///  - loops that always result in a return
    fn compile_statement(&mut self, statement: &RichStatement) -> CompileResult<bool> {
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
                return self.compile_cond(cond);
            }
            RichStatement::Loop(closure) => {
                return self.compile_loop(closure);
            }
            RichStatement::Break => {
                self.compile_break();
            }
            RichStatement::Return(ret) => {
                self.compile_return(ret);
                return Ok(true);
            }
        }

        Ok(false)
    }

    /// Compiles a break statement.
    fn compile_break(&mut self) {
        let loop_end = self.get_or_create_loop_end_block();
        self.builder.build_unconditional_branch(loop_end);
    }

    /// Compiles a loop. Returns true if the loop returns unconditionally.
    fn compile_loop(&mut self, loop_body: &RichClosure) -> CompileResult<bool> {
        // Create a new block for the loop body, and branch to it.
        let loop_begin = self.new_loop_ctx();
        self.builder.build_unconditional_branch(loop_begin);
        self.builder.position_at_end(loop_begin);

        // Compile the loop body.
        let mut returns = self.compile_closure(loop_body)?;

        // If the loop doesn't have a guaranteed return, we need to branch back to the start of the
        // loop at the end of the loop body.
        if !returns {
            self.builder.build_unconditional_branch(loop_begin);
        }

        // If there is a loop end block, it means the loop has a break and we need to continue
        // compilation on the loop end block.
        if let Some(loop_end) = self.get_loop_end_block() {
            self.builder.position_at_end(loop_end);
        } else if self.loop_has_return() {
            // At this point we know the loop contains a return but no break statements, so it
            // is guaranteed to return or run forever.
            returns = true;
        }

        // Pop the loop context now that we've compiled the loop body.
        self.pop_loop_ctx();

        Ok(returns)
    }

    /// Compiles a conditional. Returns true if all branches of the conditional result in
    /// unconditional returns.
    fn compile_cond(&mut self, cond: &RichCond) -> CompileResult<bool> {
        // Compile each branch, recording whether it returns.
        let mut end_block = None;
        let mut all_branches_return = true;
        let mut else_branch_exists = false;
        for (i, branch) in cond.branches.iter().enumerate() {
            // If there is a branch condition, it means we are on an "if" or "else if" branch.
            // Otherwise, it means we're on an "else" branch.
            if let Some(expr) = &branch.cond {
                // Create a "then" block to jump to if the branch condition is true.
                let then_block = self
                    .context
                    .append_basic_block(self.fn_value.unwrap(), format!("branch{}", i).as_str());

                // Create an "else" block to jump to if the branch condition is false.
                let else_block = self
                    .context
                    .append_basic_block(self.fn_value.unwrap(), format!("branch{}", i).as_str());

                // Branch from the current block based on the value of the conditional expression.
                let cond_val = self.get_bool(self.compile_expr(expr));
                self.builder
                    .build_conditional_branch(cond_val, then_block, else_block);

                // Fill the "then" block with the branch body.
                self.builder.position_at_end(then_block);
                let returns = self.compile_closure(&branch.body)?;
                all_branches_return &= returns;

                // If this branch does not end in an unconditional return, we need to complete
                // the corresponding "then" block with an unconditional jump to the "end" block.
                if !returns {
                    if end_block.is_none() {
                        end_block = Some(
                            self.context
                                .append_basic_block(self.fn_value.unwrap(), "endcond"),
                        );
                    }
                    self.builder.build_unconditional_branch(end_block.unwrap());
                }

                // Continue on the "else" block.
                self.builder.position_at_end(else_block);
            } else {
                // This is an else branch, so we must execute the branch body.
                else_branch_exists = true;
                let returns = self.compile_closure(&branch.body)?;
                all_branches_return &= returns;

                // If this branch does not end in an unconditional return, we need to complete
                // the current block with an unconditional jump to the "end" block.
                if !returns {
                    if end_block.is_none() {
                        end_block = Some(
                            self.context
                                .append_basic_block(self.fn_value.unwrap(), "endcond"),
                        );
                    }
                    self.builder.build_unconditional_branch(end_block.unwrap());
                }
            }
        }

        // If there is an "end" block, continue on that block.
        if let Some(block) = end_block {
            self.builder.position_at_end(block);
        }

        Ok(all_branches_return && else_branch_exists)
    }

    /// Compiles a return statement.
    fn compile_return(&mut self, ret: &RichRet) {
        if self.is_in_loop() {
            self.set_loop_has_return();
        }

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

            // RichExprKind::StringLiteral(String),
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
                "negatedbool",
            )
        } else {
            expr_val.into_int_value()
        };

        // Build the logical not as the result of the int compare != 0.
        let result = self.builder.build_int_compare(
            IntPredicate::NE,
            operand,
            self.context.bool_type().const_int(0, false),
            "test",
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
            Operator::LogicalAnd => self.builder.build_and(lhs, rhs, "and"),
            Operator::LogicalOr => self.builder.build_or(lhs, rhs, "or"),
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
    /// by a pointer to a bool.
    fn get_bool(&self, val: BasicValueEnum<'ctx>) -> IntValue<'ctx> {
        if val.is_pointer_value() {
            self.builder.build_ptr_to_int(
                val.into_pointer_value(),
                self.context.bool_type(),
                "ptrtobool",
            )
        } else {
            val.into_int_value()
        }
    }

    /// Returns the given value as an int value. This is useful for cases where the value may by
    /// a pointer to an int.
    fn get_int(&self, val: BasicValueEnum<'ctx>) -> IntValue<'ctx> {
        if val.is_pointer_value() {
            self.builder.build_ptr_to_int(
                val.into_pointer_value(),
                self.context.i64_type(),
                "ptrtoint",
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
            other => panic!("cannot dereference pointer to value of type {other}"),
        }
    }
}

/// Gets the LLVM basic type that corresponds to the given type.
fn get_basic_type<'a>(context: &'a Context, typ: &Type) -> BasicTypeEnum<'a> {
    match typ {
        Type::Bool => context.bool_type().as_basic_type_enum(),
        Type::I64 => context.i64_type().as_basic_type_enum(),
        other => {
            panic!("invalid basic type {other}");
        }
    }
}

/// Gets the LLVM "any" type that corresponds to the given type.
pub fn get_any_type<'a>(context: &'a Context, typ: Option<&Type>) -> AnyTypeEnum<'a> {
    match typ {
        None => context.void_type().as_any_type_enum(),
        Some(Type::Bool) => context.bool_type().as_any_type_enum(),
        Some(Type::I64) => context.i64_type().as_any_type_enum(),
        // TODO: string and function types
        Some(Type::Function(sig)) => {
            panic!("not implemented: {sig}")
        }
        Some(Type::String) => {
            panic!("not implemented: string")
        }
    }
}

/// Gets the LLVM metadata type that corresponds to the given type.
pub fn metadata_type_enum<'a>(context: &'a Context, typ: &Type) -> BasicMetadataTypeEnum<'a> {
    match typ {
        Type::I64 => BasicMetadataTypeEnum::from(context.i64_type()),
        Type::Bool => BasicMetadataTypeEnum::from(context.bool_type()),
        other => panic!("unsupported type {}", other),
    }
}
