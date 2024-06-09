use std::collections::HashMap;

use inkwell::attributes::{Attribute, AttributeLoc};
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::passes::PassManager;
use inkwell::types::{AnyType, BasicType, BasicTypeEnum};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue};

use crate::analyzer::ast::func::{AFn, AFnSig};
use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::type_store::{TypeKey, TypeStore};
use crate::codegen::context::{
    BranchContext, CompilationContext, FnContext, FromContext, LoopContext, StatementContext,
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
    pub fn generate(
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

    /// Returns whether the current block already has a terminator instruction.
    fn current_block_has_terminator(&self) -> bool {
        self.cur_block.unwrap().get_terminator().is_some()
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
        let cond_block = self.append_block("loop_condition");
        let body_block = self.append_block("loop_body");
        let loop_ctx = LoopContext::new(cond_block, body_block);
        self.stack.push(CompilationContext::Loop(loop_ctx));
    }

    /// Creates a new `from` context and pushes it onto the stack.
    fn push_from_ctx(&mut self) {
        let end_block = self.append_block("from_end");
        self.stack
            .push(CompilationContext::From(FromContext::new(end_block)));
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
            CompilationContext::From(ctx) => {
                ctx.guarantees_return = guarantees_return;
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
            CompilationContext::From(_) => {
                // Nothing to do here. Do expressions always guarantee a
                // terminator.
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

    /// Returns a reference to the nearest `from` context in the stack.
    fn get_from_ctx(&mut self) -> &mut FromContext<'ctx> {
        for ctx in self.stack.iter_mut().rev() {
            if let CompilationContext::From(from_ctx) = ctx {
                return from_ctx;
            }
        }

        panic!("call to get_from_ctx occurred outside of do expression");
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

    fn get_or_create_loop_update_block(&mut self) -> BasicBlock<'ctx> {
        if let Some(end_block) = self.get_loop_ctx().update_block {
            return end_block;
        }

        let update_block = self.append_block("loop_update");

        let ctx = self.get_loop_ctx();
        ctx.update_block = Some(update_block);
        ctx.update_block.unwrap()
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
        if let Some(update_block) = loop_ctx.update_block {
            update_block
        } else {
            self.get_loop_ctx().cond_block
        }
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
        let fn_val = match self
            .module
            .get_function(func.signature.mangled_name.as_str())
        {
            Some(f) => f,
            None => {
                let fn_type = self.type_converter.get_fn_type(func.signature.type_key);
                self.module.add_function(
                    func.signature.mangled_name.as_str(),
                    fn_type,
                    Some(Linkage::Internal),
                )
            }
        };

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

        // Compile the function body.
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
            fn_val.print_to_stderr();

            println!("__ BEGIN MODULE __");
            self.module.print_to_stderr();
            println!("__ END MODULE __");
            unsafe {
                fn_val.delete();
            }

            Err(CodeGenError::new(
                ErrorKind::FnVerificationFailed,
                format_code!("failed to verify function {}", func.signature.mangled_name).as_str(),
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

        let typ = self
            .type_store
            .must_get(self.type_converter.map_type_key(type_key));
        if typ.is_composite() {
            // Copy the value from the source pointer to the destination pointer.
            let ll_type_size = self
                .type_converter
                .get_basic_type(type_key)
                .size_of()
                .unwrap();

            self.builder
                .build_memcpy(
                    ll_dst_ptr,
                    2,
                    ll_src_val.into_pointer_value(),
                    2,
                    ll_type_size,
                )
                .unwrap();
        } else {
            // Store the expression value to the pointer address.
            self.builder.build_store(ll_dst_ptr, ll_src_val);
        }
    }

    /// Allocates space on the stack in the current function's entry block to store
    /// a value of the given type.
    fn stack_alloc(&mut self, name: &str, type_key: TypeKey) -> PointerValue<'ctx> {
        let ll_type = self.type_converter.get_basic_type(type_key);
        self.build_entry_alloc(name, ll_type)
    }

    /// Allocates space on the stack in the current function's entry block to store
    /// a value of the given LLVM type.
    fn build_entry_alloc(&mut self, name: &str, ll_typ: BasicTypeEnum<'ctx>) -> PointerValue<'ctx> {
        let entry = self.fn_value.unwrap().get_first_basic_block().unwrap();

        // Switch to the beginning of the entry block if we're not already there.
        let prev_block = match entry.get_first_instruction() {
            Some(first_instr) => {
                self.builder.position_before(&first_instr);
                self.cur_block
            }
            None => self.set_current_block(entry),
        };

        let ll_ptr = self
            .builder
            .build_alloca(ll_typ, format!("{}_ptr", name).as_str());

        // Make sure we continue from where we left off as our builder position may have changed
        // in this function.
        self.set_current_block(prev_block.unwrap());

        ll_ptr
    }

    /// Builds a load instruction to load data from a pointer in `ll_ptr` if
    /// `type_key` refers to a basic type that can be loaded from memory at low
    /// cost. Otherwise, just returns `ll_ptr` under the assumption that it
    /// is a composite value that can be passed as a pointer.
    fn load_if_basic(
        &mut self,
        ll_ptr: PointerValue<'ctx>,
        type_key: TypeKey,
        name: &str,
    ) -> BasicValueEnum<'ctx> {
        let typ = self.type_store.must_get(type_key);
        if typ.is_composite() {
            ll_ptr.as_basic_value_enum()
        } else {
            self.builder
                .build_load(self.type_converter.get_basic_type(type_key), ll_ptr, name)
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

/// Defines the given function in the current module based on the function signature.
pub fn gen_fn_sig<'a, 'ctx>(
    ctx: &'ctx Context,
    module: &'a Module<'ctx>,
    type_converter: &'a mut TypeConverter<'ctx>,
    sig: &AFnSig,
) {
    assert!(
        !sig.is_parameterized(),
        "unexpected generic function {}",
        sig
    );

    // Define the function in the module using the fully-qualified function name.
    let fn_type = type_converter.get_fn_type(sig.type_key);
    let fn_val = module.add_function(sig.mangled_name.as_str(), fn_type, None);

    // For now, all functions get the `frame-pointer=non-leaf` attribute. This tells
    // LLVM that the frame pointer should be kept if the function calls other functions.
    // This is important for stack unwinding.
    fn_val.add_attribute(
        AttributeLoc::Function,
        ctx.create_string_attribute("frame-pointer", "non-leaf"),
    );

    // Set arg names and mark arguments as pass-by-value where necessary.
    if fn_val.count_params() == sig.args.len() as u32 {
        // The compiled function arguments match those of the original function signature, so
        // just assign arg names normally.
        for (arg_val, arg) in fn_val.get_param_iter().zip(sig.args.iter()) {
            arg_val.set_name(arg.name.as_str());
        }
    } else {
        // The compiled function arguments do not match those of the original function
        // signature. This means the function is taking an additional pointer as its first
        // argument, to which the result will be written. This is done for functions that
        // return structured types.
        let first_arg_val = fn_val.get_first_param().unwrap();
        first_arg_val.set_name("ret_val_ptr");

        // Add the "sret" attribute to the first argument to tell LLVM that it is being used to
        // pass the return value.
        add_fn_arg_attrs(ctx, fn_val, 0, vec!["sret"]);

        // Name the remaining function arguments normally.
        for i in 1..fn_val.count_params() {
            let arg_val = fn_val.get_nth_param(i).unwrap();
            arg_val.set_name(sig.args.get((i - 1) as usize).unwrap().name.as_str());
        }
    }
}

/// Adds the given attributes to the function argument at the given index.
fn add_fn_arg_attrs<'ctx>(
    ctx: &'ctx Context,
    fn_val: FunctionValue<'ctx>,
    arg_index: u32,
    attrs: Vec<&str>,
) {
    let param = fn_val.get_nth_param(arg_index).unwrap();
    let param_type = param.get_type().as_any_type_enum();

    for attr in attrs {
        let attr_kind = Attribute::get_named_enum_kind_id(attr);
        // Make sure the attribute is properly defined.
        assert_ne!(attr_kind, 0);
        let attr = ctx.create_type_attribute(attr_kind, param_type);
        fn_val.add_attribute(AttributeLoc::Param(arg_index), attr);
    }
}
