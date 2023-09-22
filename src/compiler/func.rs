use std::collections::HashMap;

use colored::Colorize;
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
use crate::analyzer::r#struct::RichStructInit;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::analyzer::statement::RichStatement;
use crate::analyzer::var::{RichMemberAccess, RichVar};
use crate::analyzer::var_assign::RichVarAssign;
use crate::compiler::context::{
    BranchContext, CompilationContext, FnContext, LoopContext, StatementContext,
};
use crate::compiler::convert;
use crate::compiler::error::{CompileError, CompileResult, ErrorKind};
use crate::format_code;
use crate::parser::op::Operator;

/// Compiles type-rich (i.e. semantically valid) functions.
pub struct FnCompiler<'a, 'ctx> {
    ctx: &'ctx Context,
    builder: &'a Builder<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    module: &'a Module<'ctx>,

    types: &'a HashMap<TypeId, RichType>,
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
        types: &'a HashMap<TypeId, RichType>,
        func: &RichFn,
    ) -> CompileResult<FunctionValue<'ctx>> {
        let mut fn_compiler = FnCompiler {
            ctx: context,
            builder,
            fpm,
            module,
            types,
            vars: HashMap::new(),
            fn_value: None,
            stack: vec![],
            cur_block: None,
        };

        fn_compiler.compile_fn(func)
    }

    /// Creates a new basic block for this function and returns it.
    fn append_block(&mut self, name: &str) -> BasicBlock<'ctx> {
        self.ctx.append_basic_block(self.fn_value.unwrap(), name)
    }

    /// Positions at the end of `block`. Instructions created after this call will be placed at the
    /// end of `block`. Also sets `self.cur_block` to `block`. Returns the previous block.
    fn set_current_block(&mut self, block: BasicBlock<'ctx>) -> Option<BasicBlock<'ctx>> {
        let prev = self.cur_block;
        self.cur_block = Some(block);
        self.builder.position_at_end(block);
        prev
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
            CompilationContext::Func(ctx) => {
                if guarantees_term {
                    ctx.guarantees_return = true;
                }
            }
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
        // TODO: This will panic when accessing nested functions.
        let fn_val = self
            .module
            .get_function(func.signature.name.as_str())
            .unwrap();
        self.fn_value = Some(fn_val);

        // Start building from the beginning of the entry block.
        let entry = self.append_block("entry");
        self.set_current_block(entry);

        // Define function arguments as variables on the stack so they can be referenced in blocks.
        // Skip the first function argument if it is a special argument that holds the pointer to
        // the location to which the return value will be written. We'll know that this is the case
        // if the LLVM function value has one extra param (argument).
        let ll_fn_params = if fn_val.count_params() == (func.signature.args.len() + 1) as u32 {
            let mut params = fn_val.get_params();
            params.remove(0);
            params
        } else {
            fn_val.get_params()
        };

        for (ll_arg_val, arg) in ll_fn_params.into_iter().zip(func.signature.args.iter()) {
            let arg_type = self.types.get(&arg.type_id).unwrap();

            // Structs are passed as pointers and don't need to be copied to the callee stack
            // because they point to memory on the caller's stack that is safe to modify. In other
            // words, when the caller wishes to pass a struct by value, the caller will allocate
            // new space on its stack and store a copy of the struct there, and will then pass a
            // pointer to that space to the callee.
            if let RichType::Struct(_) = arg_type {
                // Create the new variable and assert that there is no other variable by the same
                // name in this function.
                assert!(self
                    .vars
                    .insert(arg.name.to_string(), ll_arg_val.into_pointer_value())
                    .is_none());
            } else {
                self.create_var(arg.name.as_str(), arg_type, ll_arg_val);
            }
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
            // TODO: this is gross
            println!("\n----BEGIN MODULE----\n");
            self.module.print_to_stderr();
            println!("----END MODULE----\n");
            fn_val.print_to_stderr();
            unsafe {
                fn_val.delete();
            }

            Err(CompileError::new(
                ErrorKind::FnVerificationFailed,
                format_code!("failed to verify {}", func.signature).as_str(),
            ))
        }
    }

    /// Allocates space on the stack for a new variable of type `typ` and writes `ll_val` to the
    /// allocated memory. Also stores a pointer to the allocated memory in `self.vars` with `name`.
    fn create_var(&mut self, name: &str, typ: &RichType, ll_val: BasicValueEnum<'ctx>) {
        let ll_dst_ptr = self.create_entry_alloc(name, typ, ll_val);
        self.copy_value(ll_val, ll_dst_ptr, typ);
        self.vars.insert(name.to_string(), ll_dst_ptr);
    }

    /// Assigns the value to the variable with the given name. Panics if no such variable exists.
    fn assign_var(&mut self, assign: &RichVarAssign) {
        // Compile the expression value being assigned.
        let ll_expr_val = self.compile_expr(&assign.val);

        // Get a pointer to the target variable (or variable member).
        let ll_var_ptr = self.get_var_ptr(&assign.var);

        // Most primitive values can be assigned (i.e. copied) with a store instruction. Composite
        // values like structs need to be copied differently.
        let var_type = self.types.get(&assign.val.type_id).unwrap();
        self.copy_value(ll_expr_val, ll_var_ptr, var_type);
    }

    /// Copies the value `ll_src_val` of type `typ` to the address pointed to by `ll_dst_ptr`.
    fn copy_value(
        &mut self,
        ll_src_val: BasicValueEnum<'ctx>,
        ll_dst_ptr: PointerValue<'ctx>,
        typ: &RichType,
    ) {
        match typ {
            RichType::Struct(struct_type) => {
                let ll_src_val_type = convert::to_basic_type(self.ctx, self.types, typ);

                // We need to copy the struct fields recursively one by one.
                for field in &struct_type.fields {
                    let field_type = self.types.get(&field.type_id).unwrap();
                    let ll_field_type = convert::to_basic_type(self.ctx, self.types, field_type);
                    let ll_field_index = struct_type.get_field_index(&field.name).unwrap() as u32;

                    // Get a pointer to the source struct field.
                    let ll_src_field_ptr = self
                        .builder
                        .build_struct_gep(
                            ll_src_val_type,
                            ll_src_val.into_pointer_value(),
                            ll_field_index,
                            format!("{}.{}_src_ptr", struct_type.name, field.name).as_str(),
                        )
                        .unwrap();

                    // Get a pointer to the destination struct field.
                    let ll_dst_field_ptr = self
                        .builder
                        .build_struct_gep(
                            ll_src_val_type,
                            ll_dst_ptr,
                            ll_field_index,
                            format!("{}.{}_dst_ptr", struct_type.name, field.name).as_str(),
                        )
                        .unwrap();

                    // Copy the field value.
                    match field_type {
                        RichType::Struct(_) => {
                            self.copy_value(
                                ll_src_field_ptr.as_basic_value_enum(),
                                ll_dst_field_ptr,
                                field_type,
                            );
                        }

                        _ => {
                            // Load the field value from the pointer.
                            let ll_src_field_val = self.builder.build_load(
                                ll_field_type,
                                ll_src_field_ptr,
                                field.name.as_str(),
                            );

                            // Copy the value to the target field pointer.
                            self.copy_value(ll_src_field_val, ll_dst_field_ptr, field_type)
                        }
                    }
                }
            }

            _ => {
                // Store the expression value to the pointer address.
                self.builder.build_store(ll_dst_ptr, ll_src_val);
            }
        }
    }

    /// Gets a pointer to the given variable or member.
    fn get_var_ptr(&self, var: &RichVar) -> PointerValue<'ctx> {
        let ll_var_ptr = self.get_var_ptr_by_name(var.var_name.as_str());
        if let Some(access) = &var.member_access {
            self.get_var_member_ptr(ll_var_ptr, &var.var_type_id, access)
        } else {
            ll_var_ptr
        }
    }

    /// Gets a variable (or member) and returns its value.
    fn get_var_value(&self, var: &RichVar) -> BasicValueEnum<'ctx> {
        // Get a pointer to the variable or member.
        let ll_var_ptr = self.get_var_ptr(var);

        // Load the value from the pointer (unless its a composite struct that is passed with
        // pointers (like structs).
        let var_type = self.types.get(&var.get_type_id()).unwrap();
        match var_type {
            RichType::Struct(_) => ll_var_ptr.as_basic_value_enum(),
            _ => {
                let ll_var_type = convert::to_basic_type(self.ctx, self.types, var_type);
                self.builder.build_load(
                    ll_var_type,
                    ll_var_ptr,
                    var.get_last_member_name().as_str(),
                )
            }
        }
    }

    /// Gets a pointer to a variable member by recursively accessing sub-members.
    /// `ll_ptr` is the pointer to the value on which the member-access is taking place.
    /// `var_type_id` is the type ID of the value pointed to by `ll_ptr`.
    /// `access` is the member (and sub-members) being accessed.
    fn get_var_member_ptr(
        &self,
        ll_ptr: PointerValue<'ctx>,
        var_type_id: &TypeId,
        access: &RichMemberAccess,
    ) -> PointerValue<'ctx> {
        let member_name = access.member_name.as_str();
        let var_type = self.types.get(var_type_id).unwrap();

        let ll_member_ptr = match var_type {
            RichType::Struct(struct_type) => {
                // Get a pointer to the struct field at the computed index.
                self.builder
                    .build_struct_gep(
                        convert::to_struct_type(self.ctx, self.types, struct_type),
                        ll_ptr,
                        struct_type.get_field_index(member_name).unwrap() as u32,
                        format!("{}_ptr", member_name).as_str(),
                    )
                    .unwrap()
            }
            other => {
                panic!("access to non-struct type {}", other)
            }
        };

        // Recursively access sub-members, if necessary.
        match &access.submember {
            Some(sub) => {
                self.get_var_member_ptr(ll_member_ptr, &access.member_type_id, sub.as_ref())
            }
            None => ll_member_ptr,
        }
    }

    /// Gets a pointer to a variable or function given its name.
    fn get_var_ptr_by_name(&self, name: &str) -> PointerValue<'ctx> {
        // Try look up the symbol as a variable.
        if let Some(ll_var_ptr) = self.vars.get(name) {
            return *ll_var_ptr;
        }

        // The symbol was not a variable, so try look it up as a function.
        if let Some(func) = self.module.get_function(name) {
            return func.as_global_value().as_pointer_value();
        }

        panic!("failed to resolve variable {}", name);
    }

    /// Creates a new stack allocation instruction in the entry block of the current function and
    /// returns a pointer to the allocated memory.
    fn create_entry_alloc(
        &mut self,
        name: &str,
        typ: &RichType,
        ll_val: BasicValueEnum<'ctx>,
    ) -> PointerValue<'ctx> {
        let entry = self.fn_value.unwrap().get_first_basic_block().unwrap();

        // Switch to the beginning of the entry block if we're not already there.
        let prev_block = match entry.get_first_instruction() {
            Some(first_instr) => {
                self.builder.position_before(&first_instr);
                self.cur_block
            }
            None => self.set_current_block(entry),
        };

        let var_name = format!("{}_ptr", name);
        let ll_ptr = if *typ == RichType::String {
            self.builder
                .build_alloca(ll_val.get_type(), var_name.as_str())
        } else {
            self.builder.build_alloca(
                convert::to_basic_type(self.ctx, self.types, typ),
                var_name.as_str(),
            )
        };

        // Make sure we continue from where we left off as our builder position may have changed
        // in this function.
        self.set_current_block(prev_block.unwrap());

        ll_ptr
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
                let ll_expr_val = self.compile_expr(&decl.val);

                // Create and initialize the variable.
                let var_type = self.types.get(&decl.type_id).unwrap();
                self.create_var(decl.name.as_str(), var_type, ll_expr_val);
            }
            RichStatement::StructTypeDeclaration(_) => {
                // Nothing to do here. Struct types are compiled upon initialization.
            }
            RichStatement::VariableAssignment(assign) => {
                self.assign_var(assign);
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
        self.set_current_block(begin_block);

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
            self.set_current_block(end_block);
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
                let ll_expr_val = self.compile_expr(expr);
                let ll_cond_val = self.get_bool(ll_expr_val);
                self.builder
                    .build_conditional_branch(ll_cond_val, then_block, else_block);

                // Fill the "then" block with the branch body.
                self.set_current_block(then_block);

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
                self.set_current_block(else_block);
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
            self.set_current_block(block);
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
            // Compile the return expression.
            Some(expr) => {
                let result = self.compile_expr(expr);

                // If the value being returned is some structured type, we need to copy it to the
                // memory pointed to by the first argument and return void.
                let expr_type = self.types.get(&expr.type_id).unwrap();
                if let RichType::Struct(_) = expr_type {
                    // Load the return value from the result pointer.
                    let expr_type = self.types.get(&expr.type_id).unwrap();
                    let ret_val = self.builder.build_load(
                        convert::to_basic_type(self.ctx, self.types, expr_type),
                        result.into_pointer_value(),
                        "ret_val",
                    );

                    // Write the return value into the pointer from the first function argument.
                    let ret_ptr = self.fn_value.unwrap().get_first_param().unwrap();
                    self.builder
                        .build_store(ret_ptr.into_pointer_value(), ret_val);

                    // Return void.
                    self.builder.build_return(None);
                } else {
                    self.builder.build_return(Some(&result));
                }
            }

            // The function has no return type, so return void.
            None => {
                self.builder.build_return(None);
            }
        }
    }

    /// Compiles an arbitrary expression.
    fn compile_expr(&mut self, expr: &RichExpr) -> BasicValueEnum<'ctx> {
        let result = match &expr.kind {
            RichExprKind::Variable(var) => self.get_var_value(var),

            RichExprKind::BoolLiteral(b) => self
                .ctx
                .bool_type()
                .const_int(*b as u64, false)
                .as_basic_value_enum(),

            RichExprKind::I64Literal(i) => self
                .ctx
                .i64_type()
                .const_int(i.abs() as u64, *i < 0)
                .as_basic_value_enum(),

            RichExprKind::StringLiteral(literal) => {
                let char_type = self.ctx.i32_type();

                // Check if this string literal already exists as a global. If not, create one.
                let global = if let Some(global) = self.module.get_global(literal) {
                    global
                } else {
                    let chars: Vec<u32> = literal.clone().chars().map(|c| c as u32).collect();

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
                    convert::to_basic_type(self.ctx, self.types, &RichType::String),
                    "str_lit_as_i32_ptr",
                )
            }

            RichExprKind::FunctionCall(call) => self.compile_call(call).unwrap(),

            RichExprKind::UnaryOperation(op, expr) => self.compile_unary_op(op, expr),

            RichExprKind::BinaryOperation(left_expr, op, right_expr) => {
                self.compile_bin_op(left_expr, op, right_expr)
            }

            RichExprKind::StructInit(struct_init) => self.compile_struct_init(struct_init),

            // TODO
            RichExprKind::AnonFunction(anon_fn) => {
                panic!("{anon_fn} not implemented");
            }

            RichExprKind::Unknown => {
                panic!("encountered unknown expression");
            }
        };

        // Dereference the result if it's a pointer.
        let expr_type = self.types.get(&expr.type_id).unwrap();
        self.deref_if_ptr(result, expr_type)
    }

    /// Compiles a struct initialization.
    fn compile_struct_init(&mut self, struct_init: &RichStructInit) -> BasicValueEnum<'ctx> {
        // Assemble the LLVM struct type.
        let ll_struct_type = convert::to_struct_type(self.ctx, self.types, &struct_init.typ);

        // Allocate space for the struct on the stack and store the zero-valued struct there.
        let ll_struct_ptr = self.builder.build_alloca(
            ll_struct_type,
            format!("{}.init_ptr", struct_init.typ.name).as_str(),
        );

        // Assign values to initialized struct fields.
        for (i, field) in struct_init.typ.fields.iter().enumerate() {
            if let Some(field_val) = struct_init.field_values.get(field.name.as_str()) {
                // Get a pointer to the struct field we're initializing.
                let ll_field_ptr = self
                    .builder
                    .build_struct_gep(
                        ll_struct_type,
                        ll_struct_ptr,
                        i as u32,
                        format!("{}.{}_ptr", struct_init.typ.name, field.name).as_str(),
                    )
                    .unwrap();

                // Compile the expression and copy its value to the struct field pointer.
                let ll_field_val = self.compile_expr(field_val);
                let field_type = self.types.get(&field.type_id).unwrap();
                self.copy_value(ll_field_val, ll_field_ptr, field_type);
            }
        }

        ll_struct_ptr.as_basic_value_enum()
    }

    /// Compiles a function call, returning the result if one exists.
    fn compile_call(&mut self, call: &RichFnCall) -> Option<BasicValueEnum<'ctx>> {
        // Get the function value from the module.
        // TODO: get functions from variables.
        let ll_fn = self
            .module
            .get_function(call.fn_var.var_name.as_str())
            .unwrap();
        let mut args: Vec<BasicMetadataValueEnum> = vec![];

        // Check if we're short one argument. If so, it means the function signature expects
        // the return value to be written to the address pointed to by the first argument, so we
        // need to add that argument. This should only be the case for functions that return
        // structured types.
        if ll_fn.count_params() == call.args.len() as u32 + 1 {
            let ret_type = self.types.get(call.ret_type_id.as_ref().unwrap()).unwrap();
            let ptr = self.builder.build_alloca(
                convert::to_basic_type(self.ctx, self.types, ret_type),
                "ret_val_ptr",
            );
            args.push(ptr.into());
        }

        // Compile call args.
        for arg in &call.args {
            // Compile the argument expression.
            let ll_arg_val = self.compile_expr(arg);

            // If the argument is a struct, we need to create a copy of it and pass a pointer to the
            // copied data instead of the original. This way, we're still passing the struct "by
            // value" (the callee can modify the data being pointed to safely, because it's a copy).
            let arg_type = self.types.get(&arg.type_id).unwrap();
            if let RichType::Struct(_) = arg_type {
                let ll_copy_ptr = self.create_entry_alloc("copy_arg", arg_type, ll_arg_val);
                self.copy_value(ll_arg_val, ll_copy_ptr, arg_type);
                args.push(ll_copy_ptr.as_basic_value_enum().into());
            } else {
                args.push(ll_arg_val.into());
            }
        }

        // Compile the function call and return the result.
        let result = self
            .builder
            .build_call(
                ll_fn,
                args.as_slice(),
                call.fn_var.get_last_member_name().as_str(),
            )
            .try_as_basic_value();

        // If there is a return value, return it. Otherwise, check if this function has a defined
        // return type. If the function has a return type and the call had no return value, it means
        // the return value was written to the address pointed to by the first function argument.
        // This will only be the case for functions that return structured values.
        if result.left().is_some() {
            result.left()
        } else if call.ret_type_id.is_some() {
            Some(
                args.first()
                    .unwrap()
                    .into_pointer_value()
                    .as_basic_value_enum(),
            )
        } else {
            None
        }
    }

    /// Compiles a unary operation expression.
    fn compile_unary_op(&mut self, op: &Operator, expr: &RichExpr) -> BasicValueEnum<'ctx> {
        // Only the not operator is supported as a unary operator at the moment.
        if *op != Operator::Not {
            panic!("unsupported unary operator {op}");
        }

        // Compile the operand expression.
        let expr_val = self.compile_expr(expr);

        // If the value is a pointer (i.e. a variable reference), we need to get the bool
        // value it points to.
        let operand = self.get_bool(expr_val);

        // Build the logical not as the result of the int compare == 0.
        let result = self.builder.build_int_compare(
            IntPredicate::EQ,
            operand,
            self.ctx.bool_type().const_int(0, false),
            ("not_".to_string() + operand.get_name().to_str().unwrap()).as_str(),
        );

        result
            .const_cast(self.ctx.bool_type(), false)
            .as_basic_value_enum()
    }

    /// Compiles a binary operation expression.
    fn compile_bin_op(
        &mut self,
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
        ll_lhs: BasicValueEnum<'ctx>,
        op: &Operator,
        ll_rhs: BasicValueEnum<'ctx>,
    ) -> IntValue<'ctx> {
        // Expect both operands to be of type bool.
        let lhs = self.get_bool(ll_lhs);
        let rhs = self.get_bool(ll_rhs);

        match op {
            Operator::LogicalAnd => self.builder.build_and(lhs, rhs, "logical_and"),
            Operator::LogicalOr => self.builder.build_or(lhs, rhs, "logical_or"),
            other => panic!("unexpected logical operator {other}"),
        }
    }

    /// Compiles a comparison operation expression.
    fn compile_cmp(
        &self,
        ll_lhs: BasicValueEnum<'ctx>,
        op: &Operator,
        ll_rhs: BasicValueEnum<'ctx>,
    ) -> IntValue<'ctx> {
        // TODO: will it work if we always treat operands as ints?
        let lhs = self.get_int(ll_lhs);
        let rhs = self.get_int(ll_rhs);

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
        ll_lhs: BasicValueEnum<'ctx>,
        op: &Operator,
        ll_rhs: BasicValueEnum<'ctx>,
    ) -> IntValue<'ctx> {
        // Expect both operands to be of type i64.
        let lhs = self.get_int(ll_lhs);
        let rhs = self.get_int(ll_rhs);

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
    fn get_bool(&self, ll_val: BasicValueEnum<'ctx>) -> IntValue<'ctx> {
        if ll_val.is_pointer_value() {
            self.builder.build_ptr_to_int(
                ll_val.into_pointer_value(),
                self.ctx.bool_type(),
                "ptr_to_bool",
            )
        } else {
            ll_val.into_int_value()
        }
    }

    /// Returns the given value as an int value. This is useful for cases where the value may be
    /// a pointer to an int.
    fn get_int(&self, ll_val: BasicValueEnum<'ctx>) -> IntValue<'ctx> {
        if ll_val.is_pointer_value() {
            self.builder.build_ptr_to_int(
                ll_val.into_pointer_value(),
                self.ctx.i64_type(),
                "ptr_to_int",
            )
        } else {
            ll_val.into_int_value()
        }
    }

    /// If the given value is a pointer, it will be dereferenced as the given type. Otherwise
    /// the value is simply returned.
    fn deref_if_ptr(&self, ll_val: BasicValueEnum<'ctx>, typ: &RichType) -> BasicValueEnum<'ctx> {
        match typ {
            // Strings an structs should already be represented as pointers.
            RichType::String | RichType::Struct(_) => ll_val,
            RichType::I64 => self.get_int(ll_val).as_basic_value_enum(),
            RichType::Bool => self.get_bool(ll_val).as_basic_value_enum(),
            RichType::Function(_) => ll_val.as_basic_value_enum(),
            RichType::Unknown(name) => {
                panic!("encountered unknown type {}", name)
            }
        }
    }
}
