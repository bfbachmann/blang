use inkwell::attributes::{Attribute, AttributeLoc};
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::{AnyType, AnyTypeEnum, BasicTypeEnum};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue};
use std::collections::{HashMap, HashSet};

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::func::{AFn, AFnSig};
use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::mangling;
use crate::analyzer::type_store::{GetType, TypeKey, TypeStore};
use crate::codegen::context::{
    BranchContext, CompilationContext, FnContext, FromContext, LoopContext, StatementContext,
};
use crate::codegen::convert::TypeConverter;
use crate::codegen::error::CodeGenResult;

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
    module: &'a Module<'ctx>,
    type_store: &'a TypeStore,
    type_converter: &'a mut TypeConverter<'ctx>,
    nested_fns: &'a HashSet<TypeKey>,
    /// Stores constant values that are declared in the module outside of functions.
    mod_consts: &'a HashMap<String, HashMap<String, AExpr>>,
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
        module: &'a Module<'ctx>,
        type_store: &'a TypeStore,
        type_converter: &'a mut TypeConverter<'ctx>,
        nested_fns: &'a HashSet<TypeKey>,
        mod_consts: &'a HashMap<String, HashMap<String, AExpr>>,
        func: &AFn,
    ) -> CodeGenResult<FunctionValue<'ctx>> {
        let mut fn_compiler = FnCodeGen {
            ctx: context,
            builder,
            module,
            type_store,
            type_converter,
            nested_fns,
            mod_consts,
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
    fn gen_fn(&mut self, func: &AFn) -> CodeGenResult<FunctionValue<'ctx>> {
        let is_nested = self.nested_fns.contains(&func.signature.type_key);
        let mangled_name = mangle_fn_name(self.type_converter, &func.signature, is_nested);

        // Retrieve the function and create a new "entry" block at the start of the function
        // body.
        let fn_val = self
            .module
            .get_function(mangled_name.as_str())
            .expect(format!("function `{}` should exist", mangled_name).as_str());

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
            let arg_type = self.type_store.get_type(arg.type_key);

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
            self.builder.build_return(None).unwrap();
        }

        // Verify and optimize the function.
        Ok(fn_val)
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
            self.builder.build_store(ll_dst_ptr, ll_src_val).unwrap();
            return;
        }

        let typ = self.type_converter.get_type(type_key);
        if typ.is_composite() {
            // Copy the value from the source pointer to the destination pointer.
            let ll_type_size = self.type_converter.const_int_size_of_type(type_key);

            // TODO: I'm not sure about the alignment here at all.
            let ll_align = self.type_converter.align_of_type(type_key);

            self.builder
                .build_memcpy(
                    ll_dst_ptr,
                    ll_align,
                    ll_src_val.into_pointer_value(),
                    ll_align,
                    ll_type_size,
                )
                .unwrap();
        } else {
            // Store the expression value to the pointer address.
            self.builder.build_store(ll_dst_ptr, ll_src_val).unwrap();
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
            .build_alloca(ll_typ, format!("{}_ptr", name).as_str())
            .unwrap();

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
        let typ = self.type_store.get_type(type_key);
        if typ.is_composite() {
            ll_ptr.as_basic_value_enum()
        } else {
            self.builder
                .build_load(self.type_converter.get_basic_type(type_key), ll_ptr, name)
                .unwrap()
        }
    }

    /// Returns the given value as a boolean int value. This is useful for cases where the value may
    /// be a pointer to a bool.
    fn get_bool(&self, ll_val: BasicValueEnum<'ctx>) -> IntValue<'ctx> {
        if ll_val.is_pointer_value() {
            self.builder
                .build_ptr_to_int(
                    ll_val.into_pointer_value(),
                    self.ctx.bool_type(),
                    "ptr_to_bool",
                )
                .unwrap()
        } else {
            ll_val.into_int_value()
        }
    }

    /// Returns the given value as an int value. This is useful for cases where the value may be
    /// a pointer to an int.
    fn get_int(&self, ll_val: BasicValueEnum<'ctx>) -> IntValue<'ctx> {
        if ll_val.is_pointer_value() {
            self.builder
                .build_ptr_to_int(
                    ll_val.into_pointer_value(),
                    self.ctx.i64_type(),
                    "ptr_to_int",
                )
                .unwrap()
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
        let enum_type = self.type_store.get_type(enum_type_key);
        let ll_enum_type = self.type_converter.get_basic_type(enum_type_key);
        let ll_variant_num_type = ll_enum_type
            .into_struct_type()
            .get_field_type_at_index(0)
            .unwrap();

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
                .build_load(ll_variant_num_type, ll_variant_ptr, "variant_number")
                .unwrap()
                .into_int_value()
        } else {
            self.builder
                .build_extract_value(ll_enum_value.into_struct_value(), 0, "variant_number")
                .unwrap()
                .into_int_value()
        }
    }

    /// If `as_ptr` is true, returns a pointer to the value field in the enum. Otherwise, returns
    /// the value itself.
    fn get_enum_inner_val(
        &mut self,
        enum_tk: TypeKey,
        inner_tk: TypeKey,
        ll_enum_value: BasicValueEnum<'ctx>,
        as_ptr: bool,
    ) -> BasicValueEnum<'ctx> {
        let ll_enum_type = self.type_converter.get_basic_type(enum_tk);
        let ll_inner_type = self.type_converter.get_basic_type(inner_tk);
        let ll_variant_type = self.ctx.struct_type(
            &[
                ll_enum_type
                    .into_struct_type()
                    .get_field_type_at_index(0)
                    .unwrap(),
                ll_inner_type,
            ],
            false,
        );

        match ll_enum_value.is_pointer_value() {
            true => {
                let ll_inner_val_ptr = self
                    .builder
                    .build_struct_gep(
                        ll_variant_type,
                        ll_enum_value.into_pointer_value(),
                        1,
                        "enum_inner_val_ptr",
                    )
                    .unwrap();

                match as_ptr {
                    true => ll_inner_val_ptr.as_basic_value_enum(),
                    false => self.load_if_basic(ll_inner_val_ptr, inner_tk, "enum_inner_val"),
                }
            }

            false => {
                assert!(
                    !as_ptr,
                    "cannot load enum inner value as pointer from non-pointer value"
                );
                self.builder
                    .build_extract_value(ll_enum_value.into_struct_value(), 1, "enum_inner_val")
                    .unwrap()
            }
        }
    }
}

/// Computes and returns the mangled name for the given function signature using the type mappings
/// in the current context.
pub fn mangle_fn_name(type_converter: &mut TypeConverter, sig: &AFnSig, is_nested: bool) -> String {
    // Re-mangle the function name, if necessary.
    let param_names = match &sig.params {
        Some(params) => mangling::mangle_param_names(params, type_converter.type_mapping()),
        None => "".to_string(),
    };

    let mut mangled_name = match sig.maybe_impl_type_key {
        Some(impl_tk) => {
            let mangled_name = mangling::remangle_type_in_name_with_mappings(
                type_converter,
                sig.mangled_name.as_str(),
                impl_tk,
                type_converter.type_mapping(),
            );
            format!("{mangled_name}{param_names}")
        }
        None => format!("{}{param_names}", sig.mangled_name),
    };

    if is_nested {
        mangled_name += mangle_type_mapping(type_converter.type_mapping()).as_str();
    }

    mangled_name
}

/// Mangles type mappings into the form `{k:v,...}` where type key `k` is mapped to `v`.
pub fn mangle_type_mapping(mapping: &HashMap<TypeKey, TypeKey>) -> String {
    let mut type_mappings: Vec<(TypeKey, TypeKey)> =
        mapping.iter().map(|(k, v)| (*k, *v)).collect();
    type_mappings.sort_by(|(k1, v1), (k2, v2)| {
        let result = k1.cmp(k2);
        match result.is_eq() {
            true => v1.cmp(v2),
            _ => result,
        }
    });

    let mut mangled_name = "{".to_string();
    for (k, v) in type_mappings {
        mangled_name += format!("{k}:{v},").as_str();
    }

    mangled_name + "}"
}

/// Defines the given function in the current module based on the function signature.
pub fn gen_fn_sig<'a, 'ctx>(
    ctx: &'ctx Context,
    module: &'a Module<'ctx>,
    type_converter: &'a mut TypeConverter<'ctx>,
    sig: &AFnSig,
    is_nested: bool,
) -> String {
    // Define the function in the module using the fully-qualified function name.
    let ll_fn_type = type_converter.get_fn_type(sig.type_key);
    let mangled_name = mangle_fn_name(type_converter, sig, is_nested);
    let ll_fn_val = module.add_function(mangled_name.as_str(), ll_fn_type, None);

    // For now, all functions get the `frame-pointer=non-leaf` attribute. This tells
    // LLVM that the frame pointer should be kept if the function calls other functions.
    // This is important for stack unwinding.
    ll_fn_val.add_attribute(
        AttributeLoc::Function,
        ctx.create_string_attribute("frame-pointer", "non-leaf"),
    );

    let args_offset = if ll_fn_val.count_params() != sig.args.len() as u32 {
        // The compiled function arguments do not match those of the original function
        // signature. This means the function is taking an additional pointer as its first
        // argument, to which the result will be written. This is done for functions that
        // return structured types.
        let first_arg_val = ll_fn_val.get_first_param().unwrap();
        first_arg_val.set_name("ret_val_ptr");
        1
    } else {
        0
    };

    // Set remaining arg names.
    for i in args_offset..ll_fn_val.count_params() {
        let arg = sig.args.get((i - args_offset) as usize).unwrap();
        let ll_arg = ll_fn_val.get_nth_param(i).unwrap();
        ll_arg.set_name(arg.name.as_str());
    }

    // Determine and attach function attributes.
    for (ll_loc, ll_attrs) in get_fn_attrs(ctx, type_converter, sig) {
        for ll_attr in ll_attrs {
            ll_fn_val.add_attribute(ll_loc, ll_attr);
        }
    }

    mangled_name.clone()
}

/// Returns LLVM attributes to set on a function declaration or call site.
pub(crate) fn get_fn_attrs(
    ctx: &Context,
    type_converter: &mut TypeConverter,
    fn_sig: &AFnSig,
) -> HashMap<AttributeLoc, Vec<Attribute>> {
    let ll_fn_type = type_converter.get_fn_type(fn_sig.type_key);
    let ll_param_count = ll_fn_type.count_param_types();
    let mut ll_attrs = HashMap::new();

    let arg_offset = if ll_param_count == fn_sig.args.len() as u32 {
        0
    } else {
        let ll_ret_type = type_converter
            .get_basic_type(fn_sig.maybe_ret_type_key.unwrap())
            .as_any_type_enum();
        ll_attrs.insert(
            AttributeLoc::Param(0),
            vec![
                new_type_attr(ctx, "sret", ll_ret_type),
                new_attr(ctx, "writeonly"),
                new_attr(ctx, "noalias"),
                new_attr(ctx, "nonnull"),
                new_attr(ctx, "nocapture"),
            ],
        );

        1
    };

    for i in arg_offset..ll_param_count {
        let arg = fn_sig.args.get((i - arg_offset) as usize).unwrap();
        let arg_type = type_converter.get_type(arg.type_key);

        if arg_type.is_composite() {
            let ll_attr_type = type_converter
                .get_basic_type(arg.type_key)
                .as_any_type_enum();

            // Mark the pointer argument as pass by value and not captured by the callee.
            let mut ll_arg_attrs = vec![
                new_type_attr(ctx, "byval", ll_attr_type),
                new_attr(ctx, "nocapture"),
            ];

            // If the argument type has non-zero size, mark it as dereferenceable up to its size.
            // Otherwise, just mark is as non-null and not undefined/poison.
            let ll_type_size = type_converter.size_of_type(arg.type_key);
            if ll_type_size > 0 {
                ll_arg_attrs.push(new_enum_attr(ctx, "dereferenceable", ll_type_size));
            } else {
                ll_arg_attrs.push(new_attr(ctx, "nonnull"));
                ll_arg_attrs.push(new_attr(ctx, "noundef"));
            }

            // Mark the pointer as readonly if the argument is immutable.
            if !arg.is_mut {
                ll_arg_attrs.push(new_attr(ctx, "readonly"));
            }

            ll_attrs.insert(AttributeLoc::Param(i), ll_arg_attrs);
        } else if arg_type.is_readonly_ptr() {
            ll_attrs.insert(AttributeLoc::Param(i), vec![new_attr(ctx, "readonly")]);
        };
    }

    ll_attrs
}

fn new_attr(ctx: &Context, name: &str) -> Attribute {
    ctx.create_enum_attribute(new_attr_kind(name), 0)
}

fn new_enum_attr(ctx: &Context, name: &str, ll_attr_val: u64) -> Attribute {
    ctx.create_enum_attribute(new_attr_kind(name), ll_attr_val)
}

pub(crate) fn new_type_attr<'ctx>(
    ctx: &'ctx Context,
    name: &str,
    ll_attr_type: AnyTypeEnum,
) -> Attribute {
    ctx.create_type_attribute(new_attr_kind(name), ll_attr_type)
}

fn new_attr_kind(name: &str) -> u32 {
    let ll_attr_kind = Attribute::get_named_enum_kind_id(name);
    assert_ne!(ll_attr_kind, 0, "invalid attribute");
    ll_attr_kind
}
