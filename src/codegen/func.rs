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
use inkwell::{AddressSpace, IntPredicate};

use crate::analyzer::ast::closure::AClosure;
use crate::analyzer::ast::cond::ACond;
use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::fn_call::AFnCall;
use crate::analyzer::ast::func::AFn;
use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::ast::r#enum::AEnumVariantInit;
use crate::analyzer::ast::r#struct::AStructInit;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::ret::ARet;
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::ast::symbol::{AMemberAccess, ASymbol};
use crate::analyzer::ast::tuple::ATupleInit;
use crate::analyzer::ast::var_assign::AVarAssign;
use crate::analyzer::type_store::{TypeKey, TypeStore};
use crate::codegen::context::{
    BranchContext, CompilationContext, FnContext, LoopContext, StatementContext,
};
use crate::codegen::convert::TypeConverter;
use crate::codegen::error::{CompileError, CompileResult, ErrorKind};
use crate::format_code;
use crate::parser::op::Operator;

/// Compiles type-rich (i.e. semantically valid) functions.
pub struct FnCodeGen<'a, 'ctx> {
    ctx: &'ctx Context,
    builder: &'a Builder<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    module: &'a Module<'ctx>,
    type_store: &'a TypeStore,
    type_converter: &'a mut TypeConverter<'ctx>,
    consts: &'a HashMap<String, AConst>,
    vars: HashMap<String, PointerValue<'ctx>>,
    fn_value: Option<FunctionValue<'ctx>>,
    stack: Vec<CompilationContext<'ctx>>,
    cur_block: Option<BasicBlock<'ctx>>,
}

impl<'a, 'ctx> FnCodeGen<'a, 'ctx> {
    /// Compiles the given function.
    pub fn compile(
        context: &'ctx Context,
        builder: &'a Builder<'ctx>,
        fpm: &'a PassManager<FunctionValue<'ctx>>,
        module: &'a Module<'ctx>,
        type_store: &'a TypeStore,
        type_converter: &'a mut TypeConverter<'ctx>,
        consts: &'a HashMap<String, AConst>,
        func: &AFn,
    ) -> CompileResult<FunctionValue<'ctx>> {
        let mut fn_compiler = FnCodeGen {
            ctx: context,
            builder,
            fpm,
            module,
            type_store,
            type_converter,
            consts,
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
    fn compile_fn(&mut self, func: &AFn) -> CompileResult<FunctionValue<'ctx>> {
        // Retrieve the function and create a new "entry" block at the start of the function
        // body.
        // TODO: This will panic when accessing nested functions.
        let fn_val = self
            .module
            .get_function(func.signature.full_name().as_str())
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
            let arg_type = self.type_store.must_get(arg.type_key);

            // Structs and tuples are passed as pointers and don't need to be copied to the callee
            // stack because they point to memory on the caller's stack that is safe to modify. In
            // other words, when the caller wishes to pass a struct by value, the caller will
            // allocate new space on its stack and store a copy of the struct there, and will then
            // pass a pointer to that space to the callee.
            if arg_type.is_composite() {
                self.vars
                    .insert(arg.name.to_string(), ll_arg_val.into_pointer_value());
            } else {
                self.create_var(arg.name.as_str(), arg.type_key, ll_arg_val);
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
                format_code!("failed to verify function {}", func.signature.full_name()).as_str(),
            ))
        }
    }

    /// Allocates space on the stack for a new variable of the type corresponding to `type_key` and
    /// writes `ll_val` to the allocated memory. Also stores a pointer to the allocated memory in
    /// `self.vars` with `name`. Returns a pointer to the new variable.
    fn create_var(
        &mut self,
        name: &str,
        type_key: TypeKey,
        ll_val: BasicValueEnum<'ctx>,
    ) -> PointerValue<'ctx> {
        let ll_dst_ptr = self.create_entry_alloc(name, type_key, ll_val);
        self.copy_value(ll_val, ll_dst_ptr, type_key);
        self.vars.insert(name.to_string(), ll_dst_ptr);
        ll_dst_ptr
    }

    /// Assigns the value to the variable with the given name. Panics if no such variable exists.
    fn assign_var(&mut self, assign: &AVarAssign) {
        // Compile the expression value being assigned.
        let ll_expr_val = self.compile_expr(&assign.val);

        // Get a pointer to the target variable (or variable member).
        let ll_var_ptr = self.get_var_ptr(&assign.symbol);

        // Most primitive values can be assigned (i.e. copied) with a store instruction. Composite
        // values like structs need to be copied differently.
        self.copy_value(ll_expr_val, ll_var_ptr, assign.val.type_key);
    }

    /// Copies the value `ll_src_val` of type `typ` to the address pointed to by `ll_dst_ptr`.
    fn copy_value(
        &mut self,
        ll_src_val: BasicValueEnum<'ctx>,
        ll_dst_ptr: PointerValue<'ctx>,
        type_key: TypeKey,
    ) {
        // If the source value is not a pointer, we don't have to copy data in memory, so we just
        // do a regular store.
        if !ll_src_val.is_pointer_value() {
            self.builder.build_store(ll_dst_ptr, ll_src_val);
            return;
        }

        let typ = self.type_store.must_get(type_key);
        match typ {
            AType::Struct(struct_type) => {
                let ll_src_val_type = self.type_converter.get_basic_type(type_key);

                // We need to copy the struct fields recursively one by one.
                for field in &struct_type.fields {
                    let field_type = self.type_store.must_get(field.type_key);
                    let ll_field_type = self.type_converter.get_basic_type(field.type_key);
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
                    if field_type.is_composite() {
                        self.copy_value(
                            ll_src_field_ptr.as_basic_value_enum(),
                            ll_dst_field_ptr,
                            field.type_key,
                        );
                    } else {
                        // Load the field value from the pointer.
                        let ll_src_field_val = self.builder.build_load(
                            ll_field_type,
                            ll_src_field_ptr,
                            field.name.as_str(),
                        );

                        // Copy the value to the target field pointer.
                        self.copy_value(ll_src_field_val, ll_dst_field_ptr, field.type_key)
                    }
                }
            }

            AType::Enum(enum_type) => {
                let ll_src_val_type = self.type_converter.get_basic_type(type_key);

                // Copy the enum number.
                let ll_enum_number = self.builder.build_load(
                    self.ctx.i8_type(),
                    ll_src_val.into_pointer_value(),
                    format!("{}.number", enum_type.name).as_str(),
                );
                self.builder.build_store(ll_dst_ptr, ll_enum_number);

                // Copy the enum variant value, if necessary.
                // TODO: does `max_variant_size_bytes` need to be even for the `memcpy` to work?
                if enum_type.max_variant_size_bytes > 0 {
                    let ll_src_value_ptr = self
                        .builder
                        .build_struct_gep(
                            ll_src_val_type,
                            ll_src_val.into_pointer_value(),
                            1u32,
                            format!("{}.src_value_ptr", enum_type.name).as_str(),
                        )
                        .unwrap();

                    let ll_dst_value_ptr = self
                        .builder
                        .build_struct_gep(
                            ll_src_val_type,
                            ll_dst_ptr,
                            1u32,
                            format!("{}.dst_value_ptr", enum_type.name).as_str(),
                        )
                        .unwrap();

                    self.builder
                        .build_memcpy(
                            ll_dst_value_ptr,
                            2,
                            ll_src_value_ptr,
                            2,
                            self.ctx
                                .i32_type()
                                .const_int(enum_type.max_variant_size_bytes as u64, false),
                        )
                        .unwrap();
                }
            }

            AType::Tuple(tuple_type) => {
                let ll_src_val_type = self.type_converter.get_basic_type(type_key);

                // We need to copy the tuple fields recursively one by one.
                for (ll_field_index, field) in tuple_type.fields.iter().enumerate() {
                    let field_type_key = field.type_key;
                    let field_type = self.type_store.must_get(field_type_key);
                    let ll_field_type = self.type_converter.get_basic_type(field_type_key);

                    // Get a pointer to the source struct field.
                    let ll_src_field_ptr = self
                        .builder
                        .build_struct_gep(
                            ll_src_val_type,
                            ll_src_val.into_pointer_value(),
                            ll_field_index as u32,
                            format!("tuple.{}_src_ptr", ll_field_index).as_str(),
                        )
                        .unwrap();

                    // Get a pointer to the destination struct field.
                    let ll_dst_field_ptr = self
                        .builder
                        .build_struct_gep(
                            ll_src_val_type,
                            ll_dst_ptr,
                            ll_field_index as u32,
                            format!("tuple.{}_dst_ptr", ll_field_index).as_str(),
                        )
                        .unwrap();

                    // Copy the field value.
                    if field_type.is_composite() {
                        self.copy_value(
                            ll_src_field_ptr.as_basic_value_enum(),
                            ll_dst_field_ptr,
                            field_type_key,
                        );
                    } else {
                        // Load the field value from the pointer.
                        let ll_src_field_val = self.builder.build_load(
                            ll_field_type,
                            ll_src_field_ptr,
                            format!("tuple.{}", ll_field_index).as_str(),
                        );

                        // Copy the value to the target field pointer.
                        self.copy_value(ll_src_field_val, ll_dst_field_ptr, field_type_key)
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
    fn get_var_ptr(&mut self, var: &ASymbol) -> PointerValue<'ctx> {
        let ll_var_ptr = self.get_var_ptr_by_name(var.name.as_str());
        if let Some(access) = &var.member_access {
            self.get_var_member_ptr(ll_var_ptr, var.parent_type_key, access)
        } else {
            ll_var_ptr
        }
    }

    /// Returns true if `var` refers directly to a function in this module. Note that this function
    /// will return false if `var` is has a function type, but refers to a local variable rather
    /// than a function defined within this module.
    fn is_var_module_fn(&self, var: &ASymbol) -> bool {
        if var.member_access.is_some() {
            false
        } else {
            self.module.get_function(var.name.as_str()).is_some()
        }
    }

    /// Gets a variable (or member) and returns its value.
    fn get_var_value(&mut self, var: &ASymbol) -> BasicValueEnum<'ctx> {
        // Get a pointer to the variable or member.
        let ll_var_ptr = self.get_var_ptr(var);

        // Load the value from the pointer (unless its a composite value that is passed with
        // pointers, or a pointer to a module-level function).
        let var_type_key = var.get_type_key();
        let var_type = self.type_store.must_get(var_type_key);
        if var_type.is_composite() || self.is_var_module_fn(var) {
            ll_var_ptr.as_basic_value_enum()
        } else {
            let ll_var_type = self.type_converter.get_basic_type(var_type_key);
            self.builder
                .build_load(ll_var_type, ll_var_ptr, var.get_last_member_name().as_str())
        }
    }

    /// Gets a pointer to a variable member by recursively accessing sub-members.
    /// `ll_ptr` is the pointer to the value on which the member-access is taking place.
    /// `var_type_key` is the type key of the value pointed to by `ll_ptr`.
    /// `access` is the member (and sub-members) being accessed.
    fn get_var_member_ptr(
        &mut self,
        ll_ptr: PointerValue<'ctx>,
        var_type_key: TypeKey,
        access: &AMemberAccess,
    ) -> PointerValue<'ctx> {
        let member_name = access.member_name.as_str();
        let var_type = self.type_store.must_get(var_type_key);

        let ll_member_ptr = match var_type {
            AType::Struct(struct_type) => {
                // Get a pointer to the struct field at the computed index.
                self.builder
                    .build_struct_gep(
                        self.type_converter.get_struct_type(var_type_key),
                        ll_ptr,
                        struct_type.get_field_index(member_name).unwrap() as u32,
                        format!("{}_ptr", member_name).as_str(),
                    )
                    .unwrap()
            }
            AType::Tuple(tuple_type) => {
                // Get a pointer to the tuple field at the computed index.
                self.builder
                    .build_struct_gep(
                        self.type_converter.get_struct_type(var_type_key),
                        ll_ptr,
                        tuple_type.get_field_index(member_name) as u32,
                        format!("{}_ptr", member_name).as_str(),
                    )
                    .unwrap()
            }
            other => {
                panic!("invalid member access of type {} on {}", other, access)
            }
        };

        // Recursively access sub-members, if necessary.
        match &access.submember {
            Some(sub) => {
                self.get_var_member_ptr(ll_member_ptr, access.member_type_key, sub.as_ref())
            }
            None => ll_member_ptr,
        }
    }

    /// Gets a pointer to a variable or function given its name.
    fn get_var_ptr_by_name(&mut self, name: &str) -> PointerValue<'ctx> {
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
        type_key: TypeKey,
        ll_val: BasicValueEnum<'ctx>,
    ) -> PointerValue<'ctx> {
        let typ = self.type_store.must_get(type_key);
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
        let ll_ptr = if *typ == AType::Str {
            self.builder
                .build_alloca(ll_val.get_type(), var_name.as_str())
        } else {
            let ll_typ = self.type_converter.get_basic_type(type_key);
            self.builder.build_alloca(ll_typ, var_name.as_str())
        };

        // Make sure we continue from where we left off as our builder position may have changed
        // in this function.
        self.set_current_block(prev_block.unwrap());

        ll_ptr
    }

    /// Compiles all statements in the closure.
    fn compile_closure(&mut self, closure: &AClosure) -> CompileResult<()> {
        for (i, statement) in closure.statements.iter().enumerate() {
            // Create a new statement context that can store information about the statement
            // we're about to compile.
            self.push_statement_ctx();

            self.compile_statement(statement)?;

            // Pop the statement context now that we've compiled the statement.
            let ctx = self.pop_ctx().to_statement();

            // If this is the last statement in the closure or the statement is guaranteed to end
            // in a terminator (unconditional jump) instruction, we need to propagate information
            // about terminators and returns to the parent context.
            if i + 1 == closure.statements.len() || ctx.guarantees_terminator {
                self.set_guarantees_return(ctx.guarantees_return);
                self.set_guarantees_terminator(ctx.guarantees_terminator);
                break;
            }
        }

        Ok(())
    }

    /// Compiles a statement.
    fn compile_statement(&mut self, statement: &AStatement) -> CompileResult<()> {
        match statement {
            AStatement::VariableDeclaration(var_decl) => {
                // Get the value of the expression being assigned to the variable.
                let ll_expr_val = self.compile_expr(&var_decl.val);

                // Create and initialize the variable.
                self.create_var(var_decl.name.as_str(), var_decl.type_key, ll_expr_val);
            }
            AStatement::StructTypeDeclaration(_) | AStatement::EnumTypeDeclaration(_) => {
                // Nothing to do here. Types are compiled upon initialization.
            }
            AStatement::VariableAssignment(assign) => {
                self.assign_var(assign);
            }
            AStatement::FunctionDeclaration(func) => {
                self.compile_fn(func)?;
            }
            AStatement::Closure(closure) => {
                self.compile_closure(closure)?;
            }
            AStatement::FunctionCall(call) => {
                self.compile_call(call);
            }
            AStatement::Conditional(cond) => {
                self.compile_cond(cond)?;
            }
            AStatement::Loop(closure) => {
                self.compile_loop(closure)?;
            }
            AStatement::Break => {
                self.compile_break();
            }
            AStatement::Continue => {
                self.compile_continue();
            }
            AStatement::Return(ret) => {
                self.compile_return(ret);
            }
            AStatement::ExternFns(_) | AStatement::Consts(_) => {
                // Nothing to do here. This is already handled in
                // `ProgramCompiler::compile_program`.
            }
            AStatement::Impl(_) => {
                // These blocks should not occur inside functions.
                unreachable!();
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
    fn compile_loop(&mut self, loop_body: &AClosure) -> CompileResult<()> {
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
    fn compile_cond(&mut self, cond: &ACond) -> CompileResult<()> {
        // Compile each branch, recording whether it returns.
        let mut end_block = None;
        let mut all_branches_return = true;
        let mut all_branches_terminate = true;
        let mut else_branch_exists = false;

        for (i, branch) in cond.branches.iter().enumerate() {
            // If there is a branch condition, it means we are on an `if` or `elsif` branch.
            // Otherwise, it means we're on an `else` branch.
            if let Some(expr) = &branch.cond {
                // Create a "then" block to jump to if the branch condition is true.
                let then_block = self.append_block("cond_branch");

                // Create an `else` block to jump to if the branch condition is false. If this is
                // the last branch in the conditional, the `else` block is the "end" block.
                // Otherwise, we create a new `else` block.
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

                // Continue on the `else` block.
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
    fn compile_return(&mut self, ret: &ARet) {
        self.set_guarantees_return(true);
        self.set_loop_contains_return(true);

        match &ret.val {
            // Compile the return expression.
            Some(expr) => {
                let result = self.compile_expr(expr);

                // If the value being returned is some structured type, we need to copy it to the
                // memory pointed to by the first argument and return void.
                let expr_type = self.type_store.must_get(expr.type_key);
                if expr_type.is_composite() {
                    // Load the return value from the result pointer.
                    let ll_ret_type = self.type_converter.get_basic_type(expr.type_key);
                    let ret_val = match result.is_pointer_value() {
                        true => self.builder.build_load(
                            ll_ret_type,
                            result.into_pointer_value(),
                            "ret_val",
                        ),
                        false => result,
                    };

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

    /// Compiles a constant expression. This is implemented separately from `compile_expr` because
    /// constant expressions are composed only of constant/immediate values that require no
    /// runtime initialization logic, whereas non-constant expressions require memory to be
    /// allocated and written to during initialization.
    /// This will probably cause a panic if `expr` is not a constant (i.e. cannot be represented
    /// by LLVM as an immediate/constant value), but the semantic analyzer should guarantee that
    /// never happens.
    fn compile_const_expr(&mut self, expr: &AExpr) -> BasicValueEnum<'ctx> {
        match &expr.kind {
            AExprKind::Symbol(symbol) => self.const_extract_value(symbol),

            AExprKind::BoolLiteral(b) => self
                .ctx
                .bool_type()
                .const_int(*b as u64, false)
                .as_basic_value_enum(),

            AExprKind::I64Literal(i, _) => self
                .ctx
                .i64_type()
                .const_int(*i as u64, *i < 0)
                .as_basic_value_enum(),

            AExprKind::U64Literal(u, _) => self
                .ctx
                .i64_type()
                .const_int(*u, false)
                .as_basic_value_enum(),

            AExprKind::Null => self
                .ctx
                .i64_type()
                .ptr_type(AddressSpace::default())
                .const_null()
                .as_basic_value_enum(),

            AExprKind::UnaryOperation(op, expr) => {
                // See note immediately below about automatic LLVM constant folding.
                self.compile_unary_op(op, expr)
            }

            AExprKind::BinaryOperation(left, op, right) => {
                // We can compile constant unary and binary operations as usual because LLVM should
                // be smart enough to do constant folding on the expressions at compile time so the
                // result is still constant.
                self.compile_bin_op(left, op, right)
            }

            AExprKind::StrLiteral(literal) => {
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
                    self.type_converter.get_basic_type(expr.type_key),
                    "str_lit_as_i32_ptr",
                )
            }

            AExprKind::TupleInit(tuple_init) => {
                let ll_struct_type = self.type_converter.get_struct_type(tuple_init.type_key);
                let ll_field_values: Vec<BasicValueEnum> = tuple_init
                    .values
                    .iter()
                    .map(|v| self.compile_const_expr(v))
                    .collect();

                ll_struct_type
                    .const_named_struct(ll_field_values.as_slice())
                    .as_basic_value_enum()
            }

            AExprKind::StructInit(struct_init) => {
                let struct_type = self
                    .type_store
                    .must_get(struct_init.type_key)
                    .to_struct_type();
                let ll_struct_type = self.type_converter.get_struct_type(struct_init.type_key);
                let mut ll_field_values = vec![];

                for field in &struct_type.fields {
                    ll_field_values.push(self.compile_const_expr(
                        struct_init.field_values.get(field.name.as_str()).unwrap(),
                    ))
                }

                ll_struct_type
                    .const_named_struct(ll_field_values.as_slice())
                    .as_basic_value_enum()
            }

            AExprKind::EnumInit(enum_init) => {
                let ll_struct_type = self.type_converter.get_struct_type(enum_init.type_key);
                let ll_variant_num = self
                    .ctx
                    .i8_type()
                    .const_int(enum_init.variant.number as u64, false)
                    .as_basic_value_enum();
                let mut ll_field_values = vec![ll_variant_num];

                // Only append the variant value if there is one.
                if let Some(val) = &enum_init.maybe_value {
                    ll_field_values.push(self.compile_const_expr(val));
                }

                ll_struct_type
                    .const_named_struct(ll_field_values.as_slice())
                    .as_basic_value_enum()
            }

            _ => panic!("unexpected const expression {}", expr),
        }
    }

    /// Compiles an arbitrary expression.
    fn compile_expr(&mut self, expr: &AExpr) -> BasicValueEnum<'ctx> {
        if expr.kind.is_const() {
            return self.compile_const_expr(expr);
        }

        let result = match &expr.kind {
            AExprKind::Symbol(var) => self.get_var_value(var),

            AExprKind::BoolLiteral(_)
            | AExprKind::I64Literal(_, _)
            | AExprKind::U64Literal(_, _)
            | AExprKind::Null
            | AExprKind::StrLiteral(_) => {
                panic!("constant expression {} was not marked as constant", expr)
            }

            AExprKind::FunctionCall(call) => self.compile_call(call).unwrap(),

            AExprKind::UnaryOperation(op, expr) => self.compile_unary_op(op, expr),

            AExprKind::BinaryOperation(left_expr, op, right_expr) => {
                self.compile_bin_op(left_expr, op, right_expr)
            }

            AExprKind::StructInit(struct_init) => self.compile_struct_init(struct_init),

            AExprKind::EnumInit(enum_init) => self.compile_enum_variant_init(enum_init),

            AExprKind::TupleInit(tuple_init) => self.compile_tuple_init(tuple_init),

            // TODO: Compiling this function works fine, but trying to actually use it will cause
            // a panic because it has no name. The fix likely involves giving anon functions unique
            // auto-generated names.
            AExprKind::AnonFunction(anon_fn) => FnCodeGen::compile(
                self.ctx,
                self.builder,
                self.fpm,
                self.module,
                self.type_store,
                self.type_converter,
                self.consts,
                anon_fn,
            )
            .unwrap()
            .as_global_value()
            .as_basic_value_enum(),

            AExprKind::Unknown => {
                panic!("encountered unknown expression");
            }
        };

        // Dereference the result if it's a pointer.
        let expr_type = self.type_store.must_get(expr.type_key);
        self.deref_if_ptr(result, expr_type)
    }

    /// Compiles tuple initialization.
    fn compile_tuple_init(&mut self, tuple_init: &ATupleInit) -> BasicValueEnum<'ctx> {
        // Assemble the LLVM struct type.
        let tuple_type = match self.type_store.must_get(tuple_init.type_key) {
            AType::Tuple(tt) => tt,
            _ => {
                panic!("unexpected type {}", tuple_init.type_key);
            }
        };
        let ll_struct_type = self.type_converter.get_struct_type(tuple_init.type_key);

        // Allocate space for the struct on the stack.
        let ll_struct_ptr = self.builder.build_alloca(ll_struct_type, "tuple_init_ptr");

        // Assign values to initialized tuple fields.
        for (i, field_val) in tuple_init.values.iter().enumerate() {
            // Get a pointer to the tuple field we're initializing.
            let ll_field_ptr = self
                .builder
                .build_struct_gep(
                    ll_struct_type,
                    ll_struct_ptr,
                    i as u32,
                    format!("tuple.{}_ptr", i).as_str(),
                )
                .unwrap();

            // Compile the expression and copy its value to the struct field pointer.
            let ll_field_val = self.compile_expr(field_val);
            let field_type_key = tuple_type.fields.get(i).unwrap().type_key;
            self.copy_value(ll_field_val, ll_field_ptr, field_type_key);
        }

        ll_struct_ptr.as_basic_value_enum()
    }

    /// Compiles enum variant initialization.
    fn compile_enum_variant_init(&mut self, enum_init: &AEnumVariantInit) -> BasicValueEnum<'ctx> {
        // Assemble the LLVM struct type for this enum value.
        let ll_struct_type = self.type_converter.get_struct_type(enum_init.type_key);

        // Allocate space for the struct on the stack.
        let ll_struct_ptr = self.builder.build_alloca(ll_struct_type, "enum_init_ptr");

        // Set the number variant number on the struct.
        let ll_number_field_ptr = self
            .builder
            .build_struct_gep(
                ll_struct_type,
                ll_struct_ptr,
                0u32,
                "enum.variant_number_ptr",
            )
            .unwrap();
        self.builder.build_store(
            ll_number_field_ptr,
            self.ctx
                .i8_type()
                .const_int(enum_init.variant.number as u64, false),
        );

        // Set the variant value field, if necessary.
        if let Some(value) = &enum_init.maybe_value {
            let ll_value = self.compile_expr(value.as_ref());
            let ll_value_field_ptr = self
                .builder
                .build_struct_gep(ll_struct_type, ll_struct_ptr, 1u32, "enum.value_ptr")
                .unwrap();

            self.copy_value(ll_value, ll_value_field_ptr, value.type_key);
        }

        ll_struct_ptr.as_basic_value_enum()
    }

    /// Compiles a struct initialization.
    fn compile_struct_init(&mut self, struct_init: &AStructInit) -> BasicValueEnum<'ctx> {
        // Assemble the LLVM struct type.
        let struct_type = self
            .type_store
            .must_get(struct_init.type_key)
            .to_struct_type();
        let ll_struct_type = self.type_converter.get_struct_type(struct_init.type_key);

        // Allocate space for the struct on the stack.
        let ll_struct_ptr = self.builder.build_alloca(
            ll_struct_type,
            format!("{}.init_ptr", struct_type.name).as_str(),
        );

        // Assign values to initialized struct fields.
        for (i, field) in struct_type.fields.iter().enumerate() {
            if let Some(field_val) = struct_init.field_values.get(field.name.as_str()) {
                // Get a pointer to the struct field we're initializing.
                let ll_field_ptr = self
                    .builder
                    .build_struct_gep(
                        ll_struct_type,
                        ll_struct_ptr,
                        i as u32,
                        format!("{}.{}_ptr", struct_type.name, field.name).as_str(),
                    )
                    .unwrap();

                // Compile the expression and copy its value to the struct field pointer.
                let ll_field_val = self.compile_expr(field_val);
                self.copy_value(ll_field_val, ll_field_ptr, field.type_key);
            }
        }

        ll_struct_ptr.as_basic_value_enum()
    }

    /// Compiles a function call, returning the result if one exists.
    fn compile_call(&mut self, call: &AFnCall) -> Option<BasicValueEnum<'ctx>> {
        // Look up the function signature and convert it to the corresponding LLVM function type.
        let fn_sig = self
            .type_store
            .must_get(call.fn_symbol.get_type_key())
            .to_fn_sig();
        let ll_fn_type = self.type_converter.get_fn_type(fn_sig.type_key);
        let mut args: Vec<BasicMetadataValueEnum> = vec![];

        // Check if we're short one argument. If so, it means the function signature expects
        // the return value to be written to the address pointed to by the first argument, so we
        // need to add that argument. This should only be the case for functions that return
        // structured types.
        if ll_fn_type.count_param_types() == call.args.len() as u32 + 1 {
            let ll_ret_type = self
                .type_converter
                .get_basic_type(call.maybe_ret_type_key.unwrap());
            let ptr = self.builder.build_alloca(ll_ret_type, "ret_val_ptr");
            args.push(ptr.into());
        }

        // Compile call args.
        for arg in &call.args {
            // Compile the argument expression.
            let ll_arg_val = self.compile_expr(arg);

            // If the argument is a structured type, we need to create a copy of it and pass a
            // pointer to the copied data instead of the original. This way, we're still passing the
            // struct "by value" (the callee can modify the data being pointed to safely, because
            // it's a copy).
            let arg_type = self.type_store.must_get(arg.type_key);
            if arg_type.is_composite() {
                let ll_copy_ptr = self.create_entry_alloc("copy_arg", arg.type_key, ll_arg_val);
                self.copy_value(ll_arg_val, ll_copy_ptr, arg.type_key);
                args.push(ll_copy_ptr.as_basic_value_enum().into());
            } else {
                args.push(ll_arg_val.into());
            }
        }

        // Compile the function call and return the result.
        let result = if self.is_var_module_fn(&call.fn_symbol) || call.is_method_call() {
            // The function is being called directly, so we can just look it up by name in the
            // module and compile this as a direct call.
            let ll_fn = self
                .module
                .get_function(fn_sig.full_name().as_str())
                .expect(
                    format!("failed to locate function {} in module", fn_sig.full_name()).as_str(),
                );
            self.builder
                .build_call(
                    ll_fn,
                    args.as_slice(),
                    call.fn_symbol.get_last_member_name().as_str(),
                )
                .try_as_basic_value()
        } else {
            // The function is actually a variable, so we need to load the function pointer from
            // the variable value and call it indirectly.
            let ll_fn_ptr = self.get_var_value(&call.fn_symbol).into_pointer_value();
            self.builder
                .build_indirect_call(
                    ll_fn_type,
                    ll_fn_ptr,
                    args.as_slice(),
                    fn_sig.full_name().as_str(),
                )
                .try_as_basic_value()
        };

        // If there is a return value, return it. Otherwise, check if this function has a defined
        // return type. If the function has a return type and the call had no return value, it means
        // the return value was written to the address pointed to by the first function argument.
        // This will only be the case for functions that return structured values.
        if result.left().is_some() {
            result.left()
        } else if call.maybe_ret_type_key.is_some() {
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
    fn compile_unary_op(&mut self, op: &Operator, expr: &AExpr) -> BasicValueEnum<'ctx> {
        // Only the not operator is supported as a unary operator at the moment.
        if *op != Operator::LogicalNot {
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
        left_expr: &AExpr,
        op: &Operator,
        right_expr: &AExpr,
    ) -> BasicValueEnum<'ctx> {
        let lhs = self.compile_expr(left_expr);

        if op == &Operator::As {
            return self
                .compile_type_cast(lhs, right_expr.type_key)
                .as_basic_value_enum();
        }

        let rhs = self.compile_expr(right_expr);

        // Determine whether the operation should be signed or unsigned based on the operand types.
        let signed = self.type_store.must_get(left_expr.type_key).is_signed();

        if op.is_arithmetic() {
            let result = self
                .compile_arith_op(lhs, op, rhs, signed)
                .as_basic_value_enum();

            // If the left operator was a pointer, then we just did pointer arithmetic and need
            // to return a pointer rather than an int.
            if lhs.is_pointer_value() {
                self.builder
                    .build_int_to_ptr(
                        result.into_int_value(),
                        self.ctx.i64_type().ptr_type(AddressSpace::default()),
                        "int_to_ptr",
                    )
                    .as_basic_value_enum()
            } else {
                result
            }
        } else if op.is_comparator() {
            self.compile_cmp(lhs, left_expr.type_key, op, rhs, signed)
                .as_basic_value_enum()
        } else if op.is_logical() {
            self.compile_logical_op(lhs, op, rhs).as_basic_value_enum()
        } else {
            panic!("unsupported operator {op}")
        }
    }

    /// Compiles a bitcast of `ll_val` to type `target_type_key`.
    fn compile_type_cast(
        &mut self,
        mut ll_val: BasicValueEnum<'ctx>,
        target_type_key: TypeKey,
    ) -> BasicValueEnum<'ctx> {
        let target_type = self.type_store.must_get(target_type_key);
        let ll_target_type = self.type_converter.get_basic_type(target_type_key);

        // TODO: When we support numeric types that are larger or smaller than 64 bits, we need to
        // think about sign extension and zero extension when casting.

        if ll_val.is_pointer_value() {
            ll_val = self
                .builder
                .build_ptr_to_int(
                    ll_val.into_pointer_value(),
                    ll_target_type.into_int_type(),
                    "ptr_as_int",
                )
                .as_basic_value_enum();
        } else if ll_target_type.is_pointer_type() {
            ll_val = self
                .builder
                .build_int_to_ptr(
                    ll_val.into_int_value(),
                    ll_target_type.into_pointer_type(),
                    "int_as_ptr",
                )
                .as_basic_value_enum();
        }

        self.builder.build_bitcast(
            ll_val,
            ll_target_type,
            format!("as_{}", target_type.name()).as_str(),
        )
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
        &mut self,
        ll_lhs: BasicValueEnum<'ctx>,
        left_type_key: TypeKey,
        op: &Operator,
        ll_rhs: BasicValueEnum<'ctx>,
        signed: bool,
    ) -> IntValue<'ctx> {
        // Handle the special case of enum variant comparisons.
        if matches!(op, Operator::Like | Operator::NotLike) {
            let ll_left_variant = self.get_enum_variant_number(left_type_key, ll_lhs);
            let ll_right_variant = self.get_enum_variant_number(left_type_key, ll_rhs);
            let predicate = match op {
                Operator::Like => IntPredicate::EQ,
                Operator::NotLike => IntPredicate::NE,
                _ => unreachable!(),
            };

            return self.builder.build_int_compare(
                predicate,
                ll_left_variant,
                ll_right_variant,
                "variants_equal",
            );
        }

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
                let ll_op = match signed {
                    true => IntPredicate::SGT,
                    false => IntPredicate::UGT,
                };
                self.builder.build_int_compare(ll_op, lhs, rhs, "gt")
            }

            Operator::LessThan => {
                let ll_op = match signed {
                    true => IntPredicate::SLT,
                    false => IntPredicate::ULT,
                };
                self.builder.build_int_compare(ll_op, lhs, rhs, "lt")
            }

            Operator::GreaterThanOrEqual => {
                let ll_op = match signed {
                    true => IntPredicate::SGE,
                    false => IntPredicate::UGE,
                };
                self.builder.build_int_compare(ll_op, lhs, rhs, "ge")
            }

            Operator::LessThanOrEqual => {
                let ll_op = match signed {
                    true => IntPredicate::SLE,
                    false => IntPredicate::ULE,
                };
                self.builder.build_int_compare(ll_op, lhs, rhs, "le")
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
        signed: bool,
    ) -> IntValue<'ctx> {
        // Expect both operands to be of some integer type.
        let lhs = self.get_int(ll_lhs);
        let rhs = self.get_int(ll_rhs);

        match op {
            Operator::Add => self.builder.build_int_add(lhs, rhs, "sum"),
            Operator::Subtract => self.builder.build_int_sub(lhs, rhs, "diff"),
            Operator::Multiply => self.builder.build_int_mul(lhs, rhs, "prod"),
            Operator::Divide => match signed {
                true => self.builder.build_int_signed_div(lhs, rhs, "quot"),
                false => self.builder.build_int_unsigned_div(lhs, rhs, "quot"),
            },
            Operator::Modulo => match signed {
                true => self.builder.build_int_signed_rem(lhs, rhs, "rem"),
                false => self.builder.build_int_unsigned_rem(lhs, rhs, "rem"),
            },
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
    fn deref_if_ptr(&self, ll_val: BasicValueEnum<'ctx>, typ: &AType) -> BasicValueEnum<'ctx> {
        match typ {
            // Strings, structs, enums, tuples, and pointers should already be represented as
            // pointers.
            AType::Str | AType::Struct(_) | AType::Enum(_) | AType::Tuple(_) | AType::Ptr => ll_val,

            AType::I64 | AType::U64 => self.get_int(ll_val).as_basic_value_enum(),

            AType::Bool => self.get_bool(ll_val).as_basic_value_enum(),

            AType::Function(_) => ll_val.as_basic_value_enum(),

            AType::Unknown(name) => {
                panic!("encountered unknown type {}", name)
            }
        }
    }

    /// Returns the variant number of the given enum. `ll_enum_value` can either be a pointer to
    /// an LLVM struct representing a Blang enum value or a constant LLVM struct.
    fn get_enum_variant_number(
        &mut self,
        enum_type_key: TypeKey,
        ll_enum_value: BasicValueEnum<'ctx>,
    ) -> IntValue<'ctx> {
        let enum_type = self.type_store.must_get(enum_type_key);
        let ll_enum_type = self.type_converter.get_basic_type(enum_type_key);

        // If the value is a pointer to an enum (i.e. the LLVM struct value representing a Blang
        // enum), then we need to use a GEP instruction to compute the address of the enum variant
        // value and then load the value from that address.
        // Otherwise, the enum value is being passed by value and we can just extract the variant
        // number from the first field in the LLVM struct.
        if ll_enum_value.is_pointer_value() {
            let ll_variant_ptr = self
                .builder
                .build_struct_gep(
                    ll_enum_type,
                    ll_enum_value.into_pointer_value(),
                    0,
                    format!("{}.variant_ptr", enum_type.name()).as_str(),
                )
                .unwrap();
            self.builder
                .build_load(self.ctx.i8_type(), ll_variant_ptr, "variant_number")
                .into_int_value()
        } else {
            self.builder
                .build_extract_value(ll_enum_value.into_struct_value(), 0, "variant_number")
                .unwrap()
                .into_int_value()
        }
    }

    /// Extracts the value of the given symbol that must represent a constant or the accesses of
    /// some field or subfield on a constant.
    fn const_extract_value(&mut self, symbol: &ASymbol) -> BasicValueEnum<'ctx> {
        let const_value = &self.consts.get(symbol.name.as_str()).unwrap().value;
        let mut ll_const_value = self.compile_const_expr(const_value);

        if symbol.member_access.is_none() {
            return ll_const_value;
        }

        let mut member_access = symbol.member_access.as_ref().unwrap();
        let mut const_type_key = const_value.type_key;

        loop {
            let member_name = &member_access.member_name;
            let const_type = self.type_store.must_get(const_type_key);
            let (ll_field_index, field_type_key) = match const_type {
                AType::Struct(struct_type) => {
                    let ll_field_index = struct_type.get_field_index(member_name.as_str()).unwrap();
                    let field_type_key = struct_type
                        .get_field_type_key(member_name.as_str())
                        .unwrap();
                    (ll_field_index as u32, field_type_key)
                }
                AType::Tuple(tuple_type) => {
                    let ll_field_index = tuple_type.get_field_index(member_name.as_str());
                    let field_type_key = tuple_type.get_field_type_key(ll_field_index).unwrap();
                    (ll_field_index as u32, field_type_key)
                }
                other => panic!("cannot extract value of non-struct type {}", other),
            };

            ll_const_value = self
                .builder
                .build_extract_value(
                    ll_const_value.into_struct_value(),
                    ll_field_index,
                    member_name.as_str(),
                )
                .unwrap();
            const_type_key = field_type_key;
            member_access = match &member_access.submember {
                Some(sm) => sm,
                None => return ll_const_value,
            };
        }
    }
}
