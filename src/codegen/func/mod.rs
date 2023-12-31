use std::collections::HashMap;

use colored::Colorize;
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue};

use crate::analyzer::ast::func::AFn;
use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::type_store::{TypeKey, TypeStore};
use crate::codegen::context::{
    BranchContext, CompilationContext, FnContext, LoopContext, StatementContext,
};
use crate::codegen::convert::TypeConverter;
use crate::codegen::error::{CodeGenError, CompileResult, ErrorKind};
use crate::format_code;

mod closure;
mod cond;
mod r#const;
mod expr;
mod r#loop;
mod statement;
mod var;

/// Uses LLVM to generate code for functions.
pub struct FnCodeGen<'a, 'ctx> {
    ctx: &'ctx Context,
    builder: &'a Builder<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    module: &'a Module<'ctx>,
    type_store: &'a TypeStore,
    type_converter: &'a mut TypeConverter<'ctx>,
    /// Stores constant values that are declared in the module outside of functions.
    module_consts: &'a HashMap<String, AConst>,
    /// Stores constant values that are declared within a function.
    local_consts: HashMap<String, AConst>,
    vars: HashMap<String, PointerValue<'ctx>>,
    fn_value: Option<FunctionValue<'ctx>>,
    stack: Vec<CompilationContext<'ctx>>,
    cur_block: Option<BasicBlock<'ctx>>,
}

impl<'a, 'ctx> FnCodeGen<'a, 'ctx> {
    /// Generates code for the given function.
    pub fn compile(
        context: &'ctx Context,
        builder: &'a Builder<'ctx>,
        fpm: &'a PassManager<FunctionValue<'ctx>>,
        module: &'a Module<'ctx>,
        type_store: &'a TypeStore,
        type_converter: &'a mut TypeConverter<'ctx>,
        module_consts: &'a HashMap<String, AConst>,
        func: &AFn,
    ) -> CompileResult<FunctionValue<'ctx>> {
        let mut fn_compiler = FnCodeGen {
            ctx: context,
            builder,
            fpm,
            module,
            type_store,
            type_converter,
            module_consts,
            local_consts: Default::default(),
            vars: HashMap::new(),
            fn_value: None,
            stack: vec![],
            cur_block: None,
        };

        fn_compiler.gen_fn(func)
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
    fn gen_fn(&mut self, func: &AFn) -> CompileResult<FunctionValue<'ctx>> {
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
        self.gen_closure(&func.body)?;

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

            Err(CodeGenError::new(
                ErrorKind::FnVerificationFailed,
                format_code!("failed to verify function {}", func.signature.full_name()).as_str(),
            ))
        }
    }

    /// Locates and returns the constant with the given name. Panics if there is no constant by
    /// that name.
    fn must_get_const(&self, name: &str) -> &AConst {
        if let Some(const_) = self.local_consts.get(name) {
            const_
        } else {
            self.module_consts.get(name).unwrap()
        }
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

    /// Dereferences `ll_val` to the given type if it is not a type that is typically represented
    /// by a pointer. Otherwise, just returns `ll_val`.
    fn maybe_deref(&self, ll_val: BasicValueEnum<'ctx>, typ: &AType) -> BasicValueEnum<'ctx> {
        match typ {
            // Strings, structs, enums, tuples, and pointers should already be represented as
            // pointers.
            AType::Str
            | AType::Struct(_)
            | AType::Enum(_)
            | AType::Tuple(_)
            | AType::Array(_)
            | AType::RawPtr
            | AType::Pointer(_) => ll_val,

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
}
