use inkwell::values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, IntValue};
use inkwell::{AddressSpace, IntPredicate};

use crate::analyzer::ast::array::AArrayInit;
use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::fn_call::AFnCall;
use crate::analyzer::ast::r#enum::AEnumVariantInit;
use crate::analyzer::ast::r#struct::AStructInit;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::tuple::ATupleInit;
use crate::analyzer::type_store::TypeKey;
use crate::parser::ast::op::Operator;

use super::FnCodeGen;

impl<'a, 'ctx> FnCodeGen<'a, 'ctx> {
    /// Compiles an arbitrary expression.
    pub(crate) fn gen_expr(&mut self, expr: &AExpr) -> BasicValueEnum<'ctx> {
        if expr.kind.is_const() {
            return self.gen_const_expr(expr);
        }

        let result = match &expr.kind {
            AExprKind::TypeCast(left_expr, target_type_key) => {
                let lhs = self.gen_expr(left_expr);
                self.gen_type_cast(lhs, *target_type_key)
                    .as_basic_value_enum()
            }

            AExprKind::Symbol(var) => self.get_var_value(var),

            AExprKind::BoolLiteral(_)
            | AExprKind::I64Literal(_, _)
            | AExprKind::U64Literal(_, _)
            | AExprKind::StrLiteral(_) => {
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
                self.module_consts,
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
        self.maybe_deref(result, expr_type)
    }

    /// Compiles tuple initialization.
    fn gen_tuple_init(&mut self, tuple_init: &ATupleInit) -> BasicValueEnum<'ctx> {
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
            let ll_field_val = self.gen_expr(field_val);
            let field_type_key = tuple_type.fields.get(i).unwrap().type_key;
            self.copy_value(ll_field_val, ll_field_ptr, field_type_key);
        }

        ll_struct_ptr.as_basic_value_enum()
    }

    /// Generates array initialization instructions and returns the resulting LLVM array value.
    fn gen_array_init(&mut self, array_init: &AArrayInit) -> BasicValueEnum<'ctx> {
        let array_type = self
            .type_store
            .must_get(array_init.type_key)
            .to_array_type();
        let ll_array_type = self.type_converter.get_array_type(array_init.type_key);

        // Allocate stack space for the array.
        let ll_array_ptr = self.builder.build_array_alloca(
            ll_array_type,
            self.ctx.i32_type().const_int(array_type.len, false),
            "array",
        );

        // Repeat array elements by cloning, if necessary.
        let elements = match &array_init.maybe_repeat_count {
            Some(count) => {
                vec![array_init.values.first().unwrap().clone(); *count as usize]
            }
            None => array_init.values.clone(),
        };

        // Init array elements.
        unsafe {
            for (i, value) in elements.iter().enumerate() {
                let ll_index = self.ctx.i32_type().const_int(i as u64, false);
                let ll_element_ptr = self.builder.build_in_bounds_gep(
                    ll_array_type,
                    ll_array_ptr,
                    &[ll_index],
                    "array_gep",
                );

                let ll_elem = self.gen_expr(value);
                self.copy_value(ll_elem, ll_element_ptr, value.type_key);
            }
        }

        ll_array_ptr.as_basic_value_enum()
    }

    /// Compiles enum variant initialization.
    fn gen_enum_variant_init(&mut self, enum_init: &AEnumVariantInit) -> BasicValueEnum<'ctx> {
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
                let ll_field_val = self.gen_expr(field_val);
                self.copy_value(ll_field_val, ll_field_ptr, field.type_key);
            }
        }

        ll_struct_ptr.as_basic_value_enum()
    }

    /// Compiles a function call, returning the result if one exists.
    pub(crate) fn gen_call(&mut self, call: &AFnCall) -> Option<BasicValueEnum<'ctx>> {
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
        for (i, arg) in call.args.iter().enumerate() {
            let arg_type = self.type_store.must_get(arg.type_key);
            let ll_arg_val = self.gen_expr(arg);

            // Make sure we write constant values that are supposed to be passed as pointers to
            // the stack and use their pointers as the arguments rather than the constant values
            // themselves.
            if arg.kind.is_const() && arg_type.is_composite() {
                let ll_arg_ptr = self.create_entry_alloc(
                    format!("arg_{}_literal", i).as_str(),
                    arg.type_key,
                    ll_arg_val,
                );

                self.copy_value(ll_arg_val, ll_arg_ptr, arg.type_key);
                args.push(ll_arg_ptr.into());
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

            Operator::Reference => match &operand_expr.kind {
                AExprKind::Symbol(symbol) if !symbol.is_const => {
                    self.get_var_ptr(symbol).as_basic_value_enum()
                }
                _ => {
                    let ll_operand_val = self.gen_expr(operand_expr);
                    let ll_ptr = self.create_entry_alloc(
                        "referenced_val",
                        operand_expr.type_key,
                        ll_operand_val,
                    );
                    self.copy_value(ll_operand_val, ll_ptr, operand_expr.type_key);
                    ll_ptr.as_basic_value_enum()
                }
            },

            Operator::Defererence => {
                // Compile the operand expression.
                let ll_operand = self.gen_expr(operand_expr);

                // Load the pointee value from the operand pointer and return it.
                let ll_pointee_type = self.type_converter.get_basic_type(result_type_key);
                self.builder.build_load(
                    ll_pointee_type,
                    ll_operand.into_pointer_value(),
                    "deref_val",
                )
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
        let lhs = self.gen_expr(left_expr);
        let rhs = self.gen_expr(right_expr);

        // Determine whether the operation should be signed or unsigned based on the operand types.
        let signed = self.type_store.must_get(left_expr.type_key).is_signed();

        if op.is_arithmetic() {
            let result = self
                .gen_arith_op(lhs, op, rhs, signed)
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
            self.gen_cmp(lhs, left_expr.type_key, op, rhs, signed)
                .as_basic_value_enum()
        } else if op.is_logical() {
            self.gen_logical_op(lhs, op, rhs).as_basic_value_enum()
        } else {
            panic!("unsupported operator {op}")
        }
    }

    /// Compiles a bitcast of `ll_val` to type `target_type_key`.
    pub(crate) fn gen_type_cast(
        &mut self,
        mut ll_val: BasicValueEnum<'ctx>,
        target_type_key: TypeKey,
    ) -> BasicValueEnum<'ctx> {
        let target_type = self.type_store.must_get(target_type_key);
        let ll_target_type = self.type_converter.get_basic_type(target_type_key);

        // TODO: When we support numeric types that are larger or smaller than 64 bits, we need to
        // think about sign extension and zero extension when casting.

        if ll_val.is_pointer_value() && ll_target_type.is_pointer_type() {
            return ll_val;
        }

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
    fn gen_logical_op(
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
    fn gen_cmp(
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

        // At this point we know it's safe to represent the types numerically for comparison.
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
    fn gen_arith_op(
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
}
