use inkwell::intrinsics::Intrinsic;
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, FloatValue, IntValue};
use inkwell::{AddressSpace, FloatPredicate, IntPredicate};
use regex::{Captures, Regex};

use crate::analyzer::ast::array::AArrayInit;
use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::fn_call::AFnCall;
use crate::analyzer::ast::func::AFnSig;
use crate::analyzer::ast::index::AIndex;
use crate::analyzer::ast::member::AMemberAccess;
use crate::analyzer::ast::r#enum::AEnumVariantInit;
use crate::analyzer::ast::r#struct::AStructInit;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::ast::tuple::ATupleInit;
use crate::analyzer::type_store::{GetType, TypeKey};
use crate::parser::ast::op::Operator;

use super::{mangle_fn_name, FnCodeGen};

impl<'a, 'ctx> FnCodeGen<'a, 'ctx> {
    /// Compiles an arbitrary expression.
    pub(crate) fn gen_expr(&mut self, expr: &AExpr) -> BasicValueEnum<'ctx> {
        if expr.kind.is_const() {
            return self.gen_const_expr(expr);
        }

        match &expr.kind {
            AExprKind::TypeCast(left_expr, target_type_key) => self
                .gen_type_cast(left_expr, *target_type_key)
                .as_basic_value_enum(),

            AExprKind::Sizeof(type_key) => self
                .type_converter
                .const_int_size_of_type(*type_key)
                .as_basic_value_enum(),

            AExprKind::Symbol(var) => self.get_var_value(var),

            AExprKind::BoolLiteral(_)
            | AExprKind::I8Literal(_)
            | AExprKind::U8Literal(_)
            | AExprKind::I16Literal(_)
            | AExprKind::U16Literal(_)
            | AExprKind::I32Literal(_)
            | AExprKind::U32Literal(_)
            | AExprKind::F32Literal(_)
            | AExprKind::I64Literal(_)
            | AExprKind::U64Literal(_)
            | AExprKind::F64Literal(_, _)
            | AExprKind::IntLiteral(_, _)
            | AExprKind::UintLiteral(_)
            | AExprKind::StrLiteral(_)
            | AExprKind::CharLiteral(_) => {
                panic!("constant expression {} was not marked as constant", expr)
            }

            AExprKind::FunctionCall(call) => self.gen_call(call).unwrap(),

            AExprKind::UnaryOperation(op, right_expr) => {
                self.gen_unary_op(op, right_expr, expr.type_key)
            }

            AExprKind::BinaryOperation(left_expr, op, right_expr) => {
                self.gen_bin_op(left_expr, op, right_expr)
            }

            AExprKind::StructInit(struct_init) => self.gen_struct_init(struct_init),

            AExprKind::EnumInit(enum_init) => self.gen_enum_variant_init(enum_init),

            AExprKind::TupleInit(tuple_init) => self.gen_tuple_init(tuple_init),

            AExprKind::ArrayInit(array_init) => self.gen_array_init(array_init),

            AExprKind::Index(index) => self.gen_index(index),

            AExprKind::AnonFunction(anon_fn) => {
                // Shouldn't need to generate anything here. The function should already
                // have been generated. We just need to return it.
                let mangled_name = mangle_fn_name(self.type_converter, &anon_fn.signature, true);
                self.module
                    .get_function(&mangled_name)
                    .expect(format!("function {mangled_name} should exist").as_str())
                    .as_global_value()
                    .as_basic_value_enum()
            }

            AExprKind::MemberAccess(access) => self.gen_member_access(access),

            AExprKind::From(statement) => self.gen_from(statement, expr.type_key),

            AExprKind::Unknown => {
                panic!("encountered unknown expression");
            }
        }
    }

    /// Generates code for a `from` expression.
    fn gen_from(
        &mut self,
        statement: &AStatement,
        result_type_key: TypeKey,
    ) -> BasicValueEnum<'ctx> {
        // Compile the statements in the `from` expression.
        self.push_from_ctx();
        self.gen_statement(statement).expect("should succeed");

        // Switch to the `from` end block and generate a phi that takes the values
        // that were yielded from incoming blocks in the `from` statement.
        let ctx = self.pop_ctx().to_from();
        self.set_current_block(ctx.end_block);

        let mut ll_result_type = self.type_converter.get_basic_type(result_type_key);
        if self.type_converter.get_type(result_type_key).is_composite() {
            // For composite types, we'll always expect yielded values to be
            // passed by reference. When we generate yield statements, we'll be
            // sure to stack-allocate composite values and yield pointers to them
            // if they're not already stack allocated.
            ll_result_type = ll_result_type
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum();
        }

        let ll_phi = self.builder.build_phi(ll_result_type, "from_result");
        for (ll_block, ll_value) in ctx.yielded_vales {
            ll_phi.add_incoming(&[(&ll_value, ll_block)]);
        }

        ll_phi.as_basic_value()
    }

    /// Compiles member access expressions.
    pub(crate) fn gen_member_access(&mut self, access: &AMemberAccess) -> BasicValueEnum<'ctx> {
        // Since method calls are detected separately in `gen_call`, if this is a method
        // then it must be a method that is being used as a variable rather than being
        // called directly.
        if access.is_method {
            let fn_sig = self
                .type_converter
                .get_type(access.member_type_key)
                .to_fn_sig();
            return self
                .module
                .get_function(fn_sig.mangled_name.as_str())
                .unwrap()
                .as_global_value()
                .as_basic_value_enum();
        }

        // At this point we know that the member access does not refer to some method,
        // so we can just generate code for the base expression the regular way
        // and then generate a member access (probably a GEP) on it.
        let ll_base_val = self.gen_expr(&access.base_expr);
        self.get_member_value(
            ll_base_val,
            access.base_expr.type_key,
            access.member_type_key,
            access.member_name.as_str(),
        )
    }

    /// Compiles tuple initialization.
    fn gen_tuple_init(&mut self, tuple_init: &ATupleInit) -> BasicValueEnum<'ctx> {
        // Assemble the LLVM struct type.
        let tuple_type = match self.type_store.get_type(tuple_init.type_key) {
            AType::Tuple(tt) => tt,
            _ => {
                panic!("unexpected type {}", tuple_init.type_key);
            }
        };
        let ll_struct_type = self.type_converter.get_struct_type(tuple_init.type_key);

        // Allocate space for the struct on the stack.
        let ll_struct_ptr = self.stack_alloc("tuple_init_ptr", tuple_init.type_key);

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
            let ll_field_val = self.gen_expr(field_val);
            let field_type_key = tuple_type.fields.get(i).unwrap().type_key;
            self.copy_value(ll_field_val, ll_field_ptr, field_type_key);
        }

        ll_struct_ptr.as_basic_value_enum()
    }

    /// Generates collection indexing expressions. Index expressions can be
    /// used to retrieve values from arrays and tuples, or to calculate pointer
    /// offsets.
    pub(crate) fn gen_index(&mut self, index: &AIndex) -> BasicValueEnum<'ctx> {
        // Generate code that gives us the collection.
        let ll_collection_val = self.gen_expr(&index.collection_expr);

        // Generate code that gives us the index value.
        let ll_index_val = self.gen_expr(&index.index_expr);

        // Generate code that retrieves the value from the collection at the
        // specified index.
        let collection_type = self.type_converter.get_type(index.collection_expr.type_key);
        match collection_type {
            AType::Tuple(_) => self.get_member_value(
                ll_collection_val,
                index.collection_expr.type_key,
                index.result_type_key,
                ll_index_val
                    .into_int_value()
                    .get_zero_extended_constant()
                    .unwrap()
                    .to_string()
                    .as_str(),
            ),

            AType::Array(_) => {
                let ll_array_type = self
                    .type_converter
                    .get_array_type(index.collection_expr.type_key);

                // Copy the collection to the stack, so we have a pointer to it that we can use for
                // the GEP below if it is not already a pointer.
                let ll_collection_ptr = if ll_collection_val.is_pointer_value() {
                    ll_collection_val.into_pointer_value()
                } else {
                    let ll_ptr = self.stack_alloc("collection", index.collection_expr.type_key);
                    self.copy_value(ll_collection_val, ll_ptr, index.collection_expr.type_key);
                    ll_ptr
                };

                // Compute the pointer to the value at the given index in the collection.
                let ll_elem_ptr = unsafe {
                    self.builder.build_in_bounds_gep(
                        ll_array_type,
                        ll_collection_ptr,
                        &[
                            self.ctx.i32_type().const_int(0, false),
                            ll_index_val.into_int_value(),
                        ],
                        "elem_ptr",
                    )
                };

                // Load the value from the pointer.
                self.load_if_basic(ll_elem_ptr, index.result_type_key, "elem")
            }

            AType::Pointer(ptr_type) => {
                // The collection is a pointer type, so we're just doing pointer
                // arithmetic.
                let ll_pointee_type = self
                    .type_converter
                    .get_basic_type(ptr_type.pointee_type_key);
                unsafe {
                    self.builder
                        .build_in_bounds_gep(
                            ll_pointee_type,
                            ll_collection_val.into_pointer_value(),
                            &[ll_index_val.into_int_value()],
                            "ptr_at_offset",
                        )
                        .as_basic_value_enum()
                }
            }

            other => panic!("unexpected collection type {other}"),
        }
    }

    /// Generates array initialization instructions and returns the resulting LLVM array value.
    pub(crate) fn gen_array_init(&mut self, array_init: &AArrayInit) -> BasicValueEnum<'ctx> {
        let array_type = self
            .type_store
            .get_type(array_init.type_key)
            .to_array_type();
        let ll_array_type = self.type_converter.get_array_type(array_init.type_key);

        // Just return a zero-array if this is an empty array type.
        if array_type.len == 0 {
            return ll_array_type.const_zero().as_basic_value_enum();
        }

        // Allocate stack space for the array.
        let ll_elem_type = self
            .type_converter
            .get_basic_type(array_init.maybe_element_type_key.unwrap());
        let ll_array_ptr = self.builder.build_array_alloca(
            ll_elem_type,
            self.ctx.i32_type().const_int(array_type.len, false),
            "array",
        );

        // If the array element is repeated multiple times, we'll generate a loop
        // that copies the value into each index in the array. Otherwise, we'll
        // just write each value into the array individually.
        match array_init.maybe_repeat_count {
            Some(repeat_count) if repeat_count > 1 => {
                let ll_loop_cond = self.append_block("array_init_cond");
                let ll_loop_body = self.append_block("array_init_body");
                let ll_loop_update = self.append_block("array_init_update");
                let ll_loop_end = self.append_block("array_init_done");

                // Init array index and jump to condition branch.
                let ll_index_type = self.ctx.i64_type();
                let ll_index_ptr =
                    self.build_entry_alloc("array_index_ptr", ll_index_type.as_basic_type_enum());
                self.builder
                    .build_store(ll_index_ptr, ll_index_type.const_int(0, false));
                self.builder.build_unconditional_branch(ll_loop_cond);

                // Check if loop index is at end of array. If so, break the loop.
                // Otherwise, continue to loop body.
                self.set_current_block(ll_loop_cond);
                let ll_index = self
                    .builder
                    .build_load(ll_index_type, ll_index_ptr, "array_index");
                let ll_continue = self.builder.build_int_compare(
                    IntPredicate::ULT,
                    ll_index.into_int_value(),
                    ll_index_type.const_int(repeat_count, false),
                    "should_continue",
                );
                self.builder
                    .build_conditional_branch(ll_continue, ll_loop_body, ll_loop_end);

                // Write the value into the current index in the array.
                self.set_current_block(ll_loop_body);
                let ll_index = self
                    .builder
                    .build_load(ll_index_type, ll_index_ptr, "array_index");
                let ll_element_ptr = unsafe {
                    self.builder.build_in_bounds_gep(
                        ll_elem_type,
                        ll_array_ptr,
                        &[ll_index.into_int_value()],
                        "array_elem_ptr",
                    )
                };
                let elem = array_init.values.get(0).unwrap();
                let ll_elem = self.gen_expr(elem);
                self.copy_value(
                    ll_elem,
                    ll_element_ptr,
                    array_init.maybe_element_type_key.unwrap(),
                );
                self.builder.build_unconditional_branch(ll_loop_update);

                // Increment the loop index and jump back to condition block.
                self.set_current_block(ll_loop_update);
                let ll_index = self
                    .builder
                    .build_load(ll_index_type, ll_index_ptr, "array_index");
                let ll_new_index = self.builder.build_int_add(
                    ll_index.into_int_value(),
                    ll_index_type.const_int(1, false),
                    "new_index",
                );
                self.builder.build_store(ll_index_ptr, ll_new_index);
                self.builder.build_unconditional_branch(ll_loop_cond);

                // Continue on loop end block.
                self.set_current_block(ll_loop_end);
            }

            _ => {
                for (i, value) in array_init.values.iter().enumerate() {
                    let ll_index = self.ctx.i32_type().const_int(i as u64, false);
                    let ll_element_ptr = unsafe {
                        self.builder.build_in_bounds_gep(
                            ll_elem_type,
                            ll_array_ptr,
                            &[ll_index],
                            "array_elem_ptr",
                        )
                    };

                    let ll_elem = self.gen_expr(value);
                    self.copy_value(ll_elem, ll_element_ptr, value.type_key);
                }
            }
        }

        ll_array_ptr.as_basic_value_enum()
    }

    /// Compiles enum variant initialization.
    fn gen_enum_variant_init(&mut self, enum_init: &AEnumVariantInit) -> BasicValueEnum<'ctx> {
        // Assemble the LLVM struct type for this enum value.
        let ll_struct_type = self.type_converter.get_struct_type(enum_init.type_key);
        let ll_variant_num_type = ll_struct_type
            .get_field_type_at_index(0)
            .unwrap()
            .into_int_type();

        // Allocate space for the struct on the stack.
        let ll_struct_ptr = self.stack_alloc("enum_init_ptr", enum_init.type_key);

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
            ll_variant_num_type.const_int(enum_init.variant.number as u64, false),
        );

        // Set the variant value field, if necessary.
        if let Some(value) = &enum_init.maybe_value {
            let ll_value = self.gen_expr(value.as_ref());
            let ll_value_field_ptr = self
                .builder
                .build_struct_gep(ll_struct_type, ll_struct_ptr, 1u32, "enum.value_ptr")
                .unwrap();

            self.copy_value(ll_value, ll_value_field_ptr, value.type_key);
        }

        ll_struct_ptr.as_basic_value_enum()
    }

    /// Compiles a struct initialization.
    fn gen_struct_init(&mut self, struct_init: &AStructInit) -> BasicValueEnum<'ctx> {
        // Assemble the LLVM struct type.
        let struct_type = self
            .type_store
            .get_type(struct_init.type_key)
            .to_struct_type();
        let ll_struct_type = self.type_converter.get_struct_type(struct_init.type_key);

        // Allocate space for the struct on the stack.
        let ll_struct_ptr = self.stack_alloc(
            format!("{}.init_ptr", struct_type.name).as_str(),
            struct_init.type_key,
        );

        // Assign values to initialized struct fields.
        for (field_name, field_value) in &struct_init.field_values {
            let field_index = struct_type.get_field_index(field_name.as_str()).unwrap();
            let field_type_key = struct_type.get_field_type_key(field_name).unwrap();

            // Get a pointer to the struct field we're initializing.
            let ll_field_ptr = self
                .builder
                .build_struct_gep(
                    ll_struct_type,
                    ll_struct_ptr,
                    field_index as u32,
                    format!("{}.{}_ptr", struct_type.name, field_name).as_str(),
                )
                .unwrap();

            // Compile the expression and copy its value to the struct field pointer.
            let ll_field_val = self.gen_expr(field_value);
            self.copy_value(ll_field_val, ll_field_ptr, field_type_key);
        }

        ll_struct_ptr.as_basic_value_enum()
    }

    /// Compiles a function call, returning the result if one exists.
    pub(crate) fn gen_call(&mut self, call: &AFnCall) -> Option<BasicValueEnum<'ctx>> {
        let fn_sig = self.type_store.get_type(call.fn_expr.type_key).to_fn_sig();

        // Check if this is a call to an intrinsic function or method. If so, we'll use
        // whatever result the custom intrinsic code generator returned.
        if let Some(result) = self.maybe_gen_intrinsic_call(call, fn_sig) {
            return Some(result);
        }

        let (mut mangled_name, ll_fn_type) = match fn_sig.maybe_impl_type_key {
            Some(impl_tk) => {
                if self.type_store.get_type(impl_tk).is_generic() {
                    // This is a function on a generic type. We need to look up the
                    // actual function by figuring out what the corresponding concrete
                    // type.
                    let concrete_tk = self.type_converter.map_type_key(impl_tk);
                    let concrete_type = self.type_store.get_type(concrete_tk);

                    // TODO: Fix demangling hack.
                    let re = Regex::new(r"(?P<prefix>[^:]*::)([^\.]*)(?P<suffix>.*)").unwrap();
                    let concrete_fn_name = re
                        .replace(fn_sig.mangled_name.as_str(), |caps: &Captures| {
                            if let Some(mangled_name) = concrete_type.maybe_mangled_name() {
                                format!("{}{}", mangled_name, &caps["suffix"])
                            } else {
                                format!(
                                    "{}{}{}",
                                    &caps["prefix"],
                                    concrete_type.name(),
                                    &caps["suffix"]
                                )
                            }
                        })
                        .into_owned();
                    let ll_fn_type = self
                        .module
                        .get_function(concrete_fn_name.as_str())
                        .expect(format!("function {} should exist", concrete_fn_name).as_str())
                        .get_type();

                    (concrete_fn_name, ll_fn_type)
                } else {
                    (
                        fn_sig.mangled_name.clone(),
                        self.type_converter.get_fn_type(fn_sig.type_key),
                    )
                }
            }

            None => (
                fn_sig.mangled_name.clone(),
                self.type_converter.get_fn_type(fn_sig.type_key),
            ),
        };

        // TODO: This is a nasty hack. Find a better way of doing this.
        let type_mapping = self.type_converter.type_mapping();
        if !type_mapping.is_empty() {
            // Define a regex to capture the part inside brackets
            let re = Regex::new(r"\[(\d+(?:,\d+)*)\]").unwrap();

            // Use `re.replace_all` to process the captured groups
            mangled_name = re
                .replace_all(mangled_name.as_str(), |caps: &regex::Captures| {
                    // Split the captured group by commas, parse integers, map them, and rejoin them
                    let mapped_numbers: Vec<String> = caps[1]
                        .split(',')
                        .filter_map(|num_str| num_str.parse::<i32>().ok())
                        .map(|num| {
                            type_mapping
                                .get(&(num as TypeKey))
                                .cloned()
                                .unwrap_or(num as TypeKey)
                        }) // Map or keep original
                        .map(|mapped_num| mapped_num.to_string()) // Convert back to string
                        .collect();

                    // Return the new bracketed string
                    format!("[{}]", mapped_numbers.join(","))
                })
                .to_string();
        }

        // Check if we're short one argument. If so, it means the function signature expects
        // the return value to be written to the address pointed to by the first argument, so we
        // need to add that argument. This should only be the case for functions that return
        // structured types.
        let mut args: Vec<BasicMetadataValueEnum> = vec![];
        if ll_fn_type.count_param_types() == call.args.len() as u32 + 1 {
            let ptr = self.stack_alloc("ret_val_ptr", call.maybe_ret_type_key.unwrap());
            args.push(ptr.into());
        }

        // Compile call args.
        for (i, arg) in call.args.iter().enumerate() {
            let arg_tk = self.type_converter.map_type_key(arg.type_key);
            let arg_type = self.type_store.get_type(arg_tk);
            let ll_arg_val = self.gen_expr(arg);

            // Make sure we write constant values that are supposed to be passed as pointers to
            // the stack and use their pointers as the arguments rather than the constant values
            // themselves.
            if !ll_arg_val.is_pointer_value() && arg_type.is_composite() {
                let ll_arg_ptr = self.stack_alloc(format!("arg_{}_literal", i).as_str(), arg_tk);

                self.copy_value(ll_arg_val, ll_arg_ptr, arg_tk);
                args.push(ll_arg_ptr.into());
            } else {
                args.push(ll_arg_val.into());
            }
        }

        // Compile the function call and return the result.
        let result = match &call.fn_expr.kind {
            AExprKind::Symbol(symbol) => {
                if self.is_var_module_fn(&symbol) || symbol.is_method {
                    // The function is being called directly, so we can just look it up by name in
                    // the module and compile this as a direct call.
                    let fn_name = self.get_full_symbol_name(symbol);
                    let ll_fn = self.module.get_function(fn_name.as_str()).expect(
                        format!("failed to locate function {} in module", fn_name).as_str(),
                    );
                    self.builder
                        .build_call(ll_fn, args.as_slice(), symbol.name.as_str())
                        .try_as_basic_value()
                } else {
                    // The function is actually a variable, so we need to load the function pointer
                    // from the variable value and call it indirectly.
                    let ll_fn_ptr = self.get_var_value(&symbol).into_pointer_value();
                    self.builder
                        .build_indirect_call(
                            ll_fn_type,
                            ll_fn_ptr,
                            args.as_slice(),
                            mangled_name.as_str(),
                        )
                        .try_as_basic_value()
                }
            }

            AExprKind::MemberAccess(access) if access.is_method => {
                let ll_fn = self.module.get_function(mangled_name.as_str()).expect(
                    format!("failed to locate function {} in module", mangled_name).as_str(),
                );
                self.builder
                    .build_call(ll_fn, args.as_slice(), access.member_name.as_str())
                    .try_as_basic_value()
            }

            _ => {
                let ll_fn_ptr = self.gen_expr(&call.fn_expr).into_pointer_value();
                self.builder
                    .build_indirect_call(
                        ll_fn_type,
                        ll_fn_ptr,
                        args.as_slice(),
                        mangled_name.as_str(),
                    )
                    .try_as_basic_value()
            }
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
    pub(crate) fn gen_unary_op(
        &mut self,
        op: &Operator,
        operand_expr: &AExpr,
        result_type_key: TypeKey,
    ) -> BasicValueEnum<'ctx> {
        match op {
            Operator::LogicalNot => {
                // Compile the operand expression.
                let ll_operand = self.gen_expr(operand_expr);

                // If the value is a pointer (i.e. a variable reference), we need to get the bool
                // value it points to.
                let int_operand = self.get_bool(ll_operand);

                // Build the logical not as the result of the int compare == 0.
                let result = self.builder.build_int_compare(
                    IntPredicate::EQ,
                    int_operand,
                    self.ctx.bool_type().const_int(0, false),
                    ("not_".to_string() + int_operand.get_name().to_str().unwrap()).as_str(),
                );

                result
                    .const_cast(self.ctx.bool_type(), false)
                    .as_basic_value_enum()
            }

            Operator::Reference | Operator::MutReference => match &operand_expr.kind {
                AExprKind::Symbol(symbol) if !symbol.is_const => {
                    self.get_var_ptr(symbol).as_basic_value_enum()
                }

                AExprKind::MemberAccess(_) | AExprKind::Index(_) => {
                    self.get_ptr_to(operand_expr).as_basic_value_enum()
                }

                _ => {
                    let ll_operand_val = self.gen_expr(operand_expr);
                    let ll_ptr = self.stack_alloc("referenced_val_ptr", operand_expr.type_key);
                    self.copy_value(ll_operand_val, ll_ptr, operand_expr.type_key);
                    ll_ptr.as_basic_value_enum()
                }
            },

            Operator::Defererence => {
                // Compile the operand expression.
                let ll_operand = self.gen_expr(operand_expr);

                // Load the pointee value from the operand pointer if necessary and return it.
                self.load_if_basic(
                    ll_operand.into_pointer_value(),
                    result_type_key,
                    "deref_val",
                )
            }

            Operator::Subtract => {
                // Compile operand expression.
                let ll_operand = self.gen_expr(operand_expr);

                // Negate the operand.
                let operand_type = self.type_store.get_type(operand_expr.type_key);
                if operand_type.is_float() {
                    self.builder
                        .build_float_neg(ll_operand.into_float_value(), "neg")
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_int_neg(ll_operand.into_int_value(), "neg")
                        .as_basic_value_enum()
                }
            }

            Operator::BitwiseNot => {
                // Compile operand expression.
                let ll_operand = self.gen_expr(operand_expr);

                // Flip the operand's bits.
                self.builder
                    .build_not(ll_operand.into_int_value(), "bnot")
                    .as_basic_value_enum()
            }

            _ => {
                panic!("unsupported unary operator {}", op)
            }
        }
    }

    /// Compiles a binary operation expression.
    pub(crate) fn gen_bin_op(
        &mut self,
        left_expr: &AExpr,
        op: &Operator,
        right_expr: &AExpr,
    ) -> BasicValueEnum<'ctx> {
        // Logical operations need to be short-circuit correctly, so we'll handle
        // them separately.
        if op.is_logical() {
            return self.gen_logical_op(left_expr, op, right_expr);
        }

        let ll_lhs = self.gen_expr(left_expr);
        let ll_rhs = self.gen_expr(right_expr);

        // Determine whether the operation should be signed or unsigned based on the operand types.
        let signed = self.type_converter.get_type(left_expr.type_key).is_signed();

        if op.is_arithmetic() {
            let result = self
                .gen_arith_op(ll_lhs, op, ll_rhs, signed)
                .as_basic_value_enum();

            // If the left operator was a pointer, then we just did pointer arithmetic and need
            // to return a pointer rather than an int.
            if ll_lhs.is_pointer_value() {
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
            self.gen_cmp_op(ll_lhs, left_expr.type_key, op, ll_rhs, signed)
                .as_basic_value_enum()
        } else {
            self.gen_bitwise_op(op, left_expr, right_expr)
                .as_basic_value_enum()
        }
    }

    /// Generates instructions that compile and bitcast `src_expr` to the given destination type.
    pub(crate) fn gen_type_cast(
        &mut self,
        src_expr: &AExpr,
        dst_type_key: TypeKey,
    ) -> BasicValueEnum<'ctx> {
        let ll_src_val = self.gen_expr(src_expr);
        let src_type = self.type_store.get_type(src_expr.type_key);
        let dst_type = self.type_store.get_type(dst_type_key);
        let ll_dst_type = self.type_converter.get_basic_type(dst_type_key);

        match (src_type, dst_type) {
            // Nothing to do here since all pointers are represented the same way in LLVM.
            (AType::Pointer(_), AType::Pointer(_))
            | (AType::Function(_), AType::Pointer(_))
            | (AType::Pointer(_), AType::Function(_)) => ll_src_val,

            // Casting `str` to a pointer.
            (AType::Str, AType::Pointer(_)) => {
                let ll_str_ptr = if ll_src_val.is_pointer_value() {
                    self.builder
                        .build_struct_gep(
                            self.ctx.i8_type(),
                            ll_src_val.into_pointer_value(),
                            1,
                            "len",
                        )
                        .unwrap()
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_extract_value(ll_src_val.into_struct_value(), 0, "ptr")
                        .unwrap()
                };

                ll_str_ptr.as_basic_value_enum()
            }

            // Casting between numeric types, or between integers and chars.
            (src, dst)
                if src.is_numeric() && dst.is_numeric()
                    || src.is_integer() && matches!(dst, AType::Char)
                    || dst.is_integer() && matches!(src, AType::Char) =>
            {
                self.gen_numeric_type_cast(ll_src_val, src_expr.type_key, dst_type_key, ll_dst_type)
            }

            // Casting from pointer to numeric type.
            (AType::Pointer(_), dst) if dst.is_numeric() => self
                .builder
                .build_ptr_to_int(
                    ll_src_val.into_pointer_value(),
                    ll_dst_type.into_int_type(),
                    "ptr_as_int",
                )
                .as_basic_value_enum(),

            // Casting from numeric type to pointer.
            (src, AType::Pointer(_)) if src.is_numeric() => self
                .builder
                .build_int_to_ptr(
                    ll_src_val.into_int_value(),
                    ll_dst_type.into_pointer_type(),
                    "int_as_ptr",
                )
                .as_basic_value_enum(),

            // Regular bitcasts.
            (_, _) => self.builder.build_bitcast(
                ll_src_val,
                ll_dst_type,
                format!("as_{}", dst_type.name()).as_str(),
            ),
        }
    }

    /// Generates a type cast between numeric types.
    fn gen_numeric_type_cast(
        &self,
        ll_src_val: BasicValueEnum<'ctx>,
        src_type_key: TypeKey,
        dst_type_key: TypeKey,
        ll_dst_type: BasicTypeEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let src_type = self.type_store.get_type(src_type_key);
        let dst_type = self.type_converter.get_type(dst_type_key);
        let src_is_signed = src_type.is_signed();
        let dst_is_signed = dst_type.is_signed();
        let src_is_float = src_type.is_float();
        let dst_is_float = dst_type.is_float();
        let src_size = self.type_converter.size_of_type(src_type_key);
        let dst_size = self.type_converter.size_of_type(dst_type_key);
        let name = format!("as_{}", dst_type.name());

        return match (src_is_float, dst_is_float, dst_is_signed) {
            // Float to float.
            (true, true, _) => self
                .builder
                .build_float_cast(
                    ll_src_val.into_float_value(),
                    ll_dst_type.into_float_type(),
                    name.as_str(),
                )
                .as_basic_value_enum(),

            // Float to signed int.
            (true, false, true) => {
                let convert_fn = Intrinsic::find("llvm.fptosi.sat")
                    .unwrap()
                    .get_declaration(self.module, &[ll_dst_type, ll_src_val.get_type()])
                    .unwrap();
                self.builder
                    .build_call(convert_fn, &[ll_src_val.into()], name.as_str())
                    .try_as_basic_value()
                    .left()
                    .unwrap()
            }

            // Float to unsigned int.
            (true, false, false) => {
                let convert_fn = Intrinsic::find("llvm.fptoui.sat")
                    .unwrap()
                    .get_declaration(self.module, &[ll_dst_type, ll_src_val.get_type()])
                    .unwrap();
                self.builder
                    .build_call(convert_fn, &[ll_src_val.into()], name.as_str())
                    .try_as_basic_value()
                    .left()
                    .unwrap()
            }

            // Int to int.
            (false, false, _) => {
                if src_size <= dst_size {
                    if src_is_signed {
                        // Sign-extended upcasts.
                        self.builder
                            .build_int_s_extend_or_bit_cast(
                                ll_src_val.into_int_value(),
                                ll_dst_type.into_int_type(),
                                name.as_str(),
                            )
                            .as_basic_value_enum()
                    } else {
                        // Zero-extended upcasts.
                        return self
                            .builder
                            .build_int_z_extend_or_bit_cast(
                                ll_src_val.into_int_value(),
                                ll_dst_type.into_int_type(),
                                name.as_str(),
                            )
                            .as_basic_value_enum();
                    }
                } else {
                    // Truncating downcasts.
                    self.builder
                        .build_int_truncate_or_bit_cast(
                            ll_src_val.into_int_value(),
                            ll_dst_type.into_int_type(),
                            name.as_str(),
                        )
                        .as_basic_value_enum()
                }
            }

            // Int to float.
            (false, true, _) => {
                if src_is_signed {
                    self.builder
                        .build_signed_int_to_float(
                            ll_src_val.into_int_value(),
                            ll_dst_type.into_float_type(),
                            name.as_str(),
                        )
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_unsigned_int_to_float(
                            ll_src_val.into_int_value(),
                            ll_dst_type.into_float_type(),
                            name.as_str(),
                        )
                        .as_basic_value_enum()
                }
            }
        };
    }

    /// Compiles a logical (boolean) operation expression. These operations
    /// short-circuit the same way they would in C. In other words:
    ///  - for logical and, the right expression is only evaluated if the left
    ///    is true
    ///  - for logical or, the right expression is only evaluated if the left is
    ///    false.
    fn gen_logical_op(
        &mut self,
        left_expr: &AExpr,
        op: &Operator,
        right_expr: &AExpr,
    ) -> BasicValueEnum<'ctx> {
        let right_block = self.append_block(format!("logical_{}_rhs", op).as_str());
        let end_block = self.append_block(format!("logical_{}_end", op).as_str());

        // Generate code for the left expression.
        let ll_lhs = self.gen_expr(left_expr);
        let ll_lhs = self.get_int(ll_lhs);
        let left_block = self.cur_block.unwrap();

        // Either short-circuit or compute the right expression based on the
        // left value.
        if op == &Operator::LogicalAnd {
            self.builder
                .build_conditional_branch(ll_lhs, right_block, end_block);
        } else {
            self.builder
                .build_conditional_branch(ll_lhs, end_block, right_block);
        }

        // Generate code for the right expression.
        self.set_current_block(right_block);
        let ll_rhs = self.gen_expr(right_expr);
        let ll_rhs = self.get_int(ll_rhs);
        self.builder.build_unconditional_branch(end_block);

        // Generate code that computes the result of the logical operation
        // based on the results from the two branches.
        self.set_current_block(end_block);
        let ll_phi = self
            .builder
            .build_phi(self.ctx.bool_type(), "logical_op_result");
        ll_phi.add_incoming(&[(&ll_lhs, left_block)]);
        ll_phi.add_incoming(&[(&ll_rhs, right_block)]);
        ll_phi.as_basic_value()
    }

    /// Compiles a comparison operation expression.
    pub(crate) fn gen_cmp_op(
        &mut self,
        mut ll_lhs: BasicValueEnum<'ctx>,
        left_type_key: TypeKey,
        op: &Operator,
        mut ll_rhs: BasicValueEnum<'ctx>,
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

        // Handle the special case of `str` comparisons.
        let left_type = self.type_store.get_type(left_type_key);
        if left_type == &AType::Str {
            ll_lhs = self
                .builder
                .build_extract_value(ll_lhs.into_struct_value(), 0, "left_ptr")
                .unwrap()
                .as_basic_value_enum();
            ll_rhs = self
                .builder
                .build_extract_value(ll_rhs.into_struct_value(), 0, "right_ptr")
                .unwrap()
                .as_basic_value_enum();
        }

        // Handle the special case of floating point comparisons.
        if left_type.is_float() {
            return self.gen_float_cmp_op(op, ll_lhs, ll_rhs);
        }

        // At this point we know it's safe to represent the types as ints for comparison.
        self.gen_int_cmp(op, ll_lhs, ll_rhs, signed)
    }

    /// Generates code for bitwise operations.
    fn gen_bitwise_op(
        &mut self,
        op: &Operator,
        left_expr: &AExpr,
        right_expr: &AExpr,
    ) -> IntValue<'ctx> {
        let ll_lhs = self.gen_expr(left_expr).into_int_value();
        let ll_rhs = self.gen_expr(right_expr).into_int_value();

        match op {
            Operator::BitwiseAnd => self.builder.build_and(ll_lhs, ll_rhs, "band"),
            Operator::BitwiseOr => self.builder.build_or(ll_lhs, ll_rhs, "bor"),
            Operator::BitwiseXor => self.builder.build_xor(ll_lhs, ll_rhs, "bxor"),
            Operator::BitwiseLeftShift => self.builder.build_left_shift(ll_lhs, ll_rhs, "bls"),
            Operator::BitwiseRightShift => {
                self.builder.build_right_shift(ll_lhs, ll_rhs, false, "brs")
            }
            _ => panic!("unexpected bitwise operator {op}"),
        }
    }

    /// Generates code for floating-point value comparisons.
    fn gen_float_cmp_op(
        &mut self,
        op: &Operator,
        ll_lhs: BasicValueEnum<'ctx>,
        ll_rhs: BasicValueEnum<'ctx>,
    ) -> IntValue<'ctx> {
        let lhs = ll_lhs.into_float_value();
        let rhs = ll_rhs.into_float_value();

        match op {
            Operator::EqualTo => {
                self.builder
                    .build_float_compare(FloatPredicate::OEQ, lhs, rhs, "eq")
            }

            Operator::NotEqualTo => {
                self.builder
                    .build_float_compare(FloatPredicate::ONE, lhs, rhs, "ne")
            }

            Operator::GreaterThan => {
                self.builder
                    .build_float_compare(FloatPredicate::OGT, lhs, rhs, "gt")
            }

            Operator::LessThan => {
                self.builder
                    .build_float_compare(FloatPredicate::OLT, lhs, rhs, "lt")
            }

            Operator::GreaterThanOrEqual => {
                self.builder
                    .build_float_compare(FloatPredicate::OGE, lhs, rhs, "ge")
            }

            Operator::LessThanOrEqual => {
                self.builder
                    .build_float_compare(FloatPredicate::OLE, lhs, rhs, "le")
            }

            other => panic!("unexpected comparison operator {other}"),
        }
    }

    /// Generates code for integer value comparisons.
    pub fn gen_int_cmp(
        &mut self,
        op: &Operator,
        ll_lhs: BasicValueEnum<'ctx>,
        ll_rhs: BasicValueEnum<'ctx>,
        signed: bool,
    ) -> IntValue<'ctx> {
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

    /// Generates code an arithmetic operation on integer or floating-point
    /// values.
    fn gen_arith_op(
        &self,
        ll_lhs: BasicValueEnum<'ctx>,
        op: &Operator,
        ll_rhs: BasicValueEnum<'ctx>,
        signed: bool,
    ) -> BasicValueEnum<'ctx> {
        if ll_lhs.is_float_value() {
            self.gen_float_arith_op(ll_lhs.into_float_value(), op, ll_rhs.into_float_value())
                .as_basic_value_enum()
        } else {
            self.gen_int_arith_op(ll_lhs, op, ll_rhs, signed)
                .as_basic_value_enum()
        }
    }

    /// Compiles an integer arithmetic binary operation expression.
    /// This function accepts operands as basic values instead of int values
    /// as the arguments could be integers or pointers.
    fn gen_int_arith_op(
        &self,
        ll_lhs: BasicValueEnum<'ctx>,
        op: &Operator,
        ll_rhs: BasicValueEnum<'ctx>,
        signed: bool,
    ) -> IntValue<'ctx> {
        // Expect both operands to be of some integer type (pointers are ints).
        let ll_lhs = self.get_int(ll_lhs);
        let ll_rhs = self.get_int(ll_rhs);

        match op {
            Operator::Add => self.builder.build_int_add(ll_lhs, ll_rhs, "sum"),
            Operator::Subtract => self.builder.build_int_sub(ll_lhs, ll_rhs, "diff"),
            Operator::Multiply => self.builder.build_int_mul(ll_lhs, ll_rhs, "prod"),
            Operator::Divide => match signed {
                true => self.builder.build_int_signed_div(ll_lhs, ll_rhs, "quot"),
                false => self.builder.build_int_unsigned_div(ll_lhs, ll_rhs, "quot"),
            },
            Operator::Modulo => match signed {
                true => self.builder.build_int_signed_rem(ll_lhs, ll_rhs, "rem"),
                false => self.builder.build_int_unsigned_rem(ll_lhs, ll_rhs, "rem"),
            },
            other => panic!("unexpected arithmetic operator {other}"),
        }
    }

    /// Compiles a floating-point arithmetic binary operation expression.
    fn gen_float_arith_op(
        &self,
        ll_lhs: FloatValue<'ctx>,
        op: &Operator,
        ll_rhs: FloatValue<'ctx>,
    ) -> FloatValue<'ctx> {
        match op {
            Operator::Add => self.builder.build_float_add(ll_lhs, ll_rhs, "sum"),
            Operator::Subtract => self.builder.build_float_sub(ll_lhs, ll_rhs, "diff"),
            Operator::Multiply => self.builder.build_float_mul(ll_lhs, ll_rhs, "prod"),
            Operator::Divide => self.builder.build_float_div(ll_lhs, ll_rhs, "quot"),
            Operator::Modulo => self.builder.build_float_rem(ll_lhs, ll_rhs, "rem"),
            other => panic!("unexpected arithmetic operator {other}"),
        }
    }

    /// Checks if the given function call is a call to an intrinsic function. If so,
    /// generates code for the intrinsic function call and returns the result.
    fn maybe_gen_intrinsic_call(
        &mut self,
        call: &AFnCall,
        fn_sig: &AFnSig,
    ) -> Option<BasicValueEnum<'ctx>> {
        if fn_sig.mangled_name.ends_with(".clone")
            && fn_sig
                .maybe_impl_type_key
                .is_some_and(|tk| self.type_converter.get_type(tk).is_primitive())
        {
            // Compile the `*self` argument expression.
            let ll_self_arg = self.gen_expr(call.args.first().unwrap());
            let ll_pointee_type = self
                .type_converter
                .get_basic_type(fn_sig.maybe_impl_type_key.unwrap());
            return Some(self.builder.build_load(
                ll_pointee_type,
                ll_self_arg.into_pointer_value(),
                "cloned",
            ));
        }

        None
    }
}
