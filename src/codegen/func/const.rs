use inkwell::values::{
    ArrayValue, BasicValue, BasicValueEnum, FloatValue, IntValue, PointerValue, StructValue,
};

use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::symbol::ASymbol;

use super::FnCodeGen;

impl<'a, 'ctx> FnCodeGen<'a, 'ctx> {
    /// Compiles a constant expression. This is implemented separately from `gen_expr` because
    /// constant expressions are composed only of constant/immediate values that require no
    /// runtime initialization logic, whereas non-constant expressions require memory to be
    /// allocated and written to during initialization.
    /// This will probably cause a panic if `expr` is not a constant (i.e. cannot be represented
    /// by LLVM as an immediate/constant value), but the semantic analyzer should guarantee that
    /// never happens.
    pub(crate) fn gen_const_expr(&mut self, expr: &AExpr) -> BasicValueEnum<'ctx> {
        match &expr.kind {
            AExprKind::Symbol(symbol) => self.const_extract_value(symbol),

            AExprKind::BoolLiteral(b) => self
                .ctx
                .bool_type()
                .const_int(*b as u64, false)
                .as_basic_value_enum(),

            AExprKind::I8Literal(i) => self
                .ctx
                .i8_type()
                .const_int(*i as u64, *i < 0)
                .as_basic_value_enum(),

            AExprKind::U8Literal(u) => self
                .ctx
                .i8_type()
                .const_int(*u as u64, false)
                .as_basic_value_enum(),

            AExprKind::I16Literal(i) => self
                .ctx
                .i16_type()
                .const_int(*i as u64, *i < 0)
                .as_basic_value_enum(),

            AExprKind::U16Literal(u) => self
                .ctx
                .i16_type()
                .const_int(*u as u64, false)
                .as_basic_value_enum(),

            AExprKind::I32Literal(i) => self
                .ctx
                .i32_type()
                .const_int(*i as u64, *i < 0)
                .as_basic_value_enum(),

            AExprKind::U32Literal(u) => self
                .ctx
                .i32_type()
                .const_int(*u as u64, false)
                .as_basic_value_enum(),

            AExprKind::F32Literal(f) => self
                .ctx
                .f32_type()
                .const_float(*f as f64)
                .as_basic_value_enum(),

            AExprKind::I64Literal(i) => self
                .ctx
                .i64_type()
                .const_int(*i as u64, *i < 0)
                .as_basic_value_enum(),

            AExprKind::U64Literal(u) => self
                .ctx
                .i64_type()
                .const_int(*u, false)
                .as_basic_value_enum(),

            AExprKind::F64Literal(f, _) => {
                self.ctx.f64_type().const_float(*f).as_basic_value_enum()
            }

            AExprKind::IntLiteral(i, _) => self
                .type_converter
                .get_basic_type(expr.type_key)
                .into_int_type()
                .const_int(*i as u64, *i < 0)
                .as_basic_value_enum(),

            AExprKind::UintLiteral(u) => self
                .type_converter
                .get_basic_type(expr.type_key)
                .into_int_type()
                .const_int(*u, false)
                .as_basic_value_enum(),

            AExprKind::UnaryOperation(op, operand_expr) => {
                // See note immediately below about automatic LLVM constant folding.
                self.gen_unary_op(op, operand_expr, expr.type_key)
            }

            AExprKind::BinaryOperation(left, op, right) => {
                // We can compile constant unary and binary operations as usual because LLVM should
                // be smart enough to do constant folding on the expressions at compile time so the
                // result is still constant.
                self.gen_bin_op(left, op, right)
            }

            AExprKind::StrLiteral(literal) => {
                let char_type = self.ctx.i8_type();

                // Check if this string literal already exists as a global. If not, create one.
                let global = if let Some(global) = self.module.get_global(literal) {
                    global
                } else {
                    let chars: Vec<u8> = literal.clone().into_bytes();
                    let array_type = char_type.array_type((chars.len()) as u32);
                    let array_vals: Vec<_> = chars
                        .iter()
                        .map(|v| char_type.const_int((*v).into(), false))
                        .collect();

                    let global = self.module.add_global(array_type, None, literal.as_str());
                    global.set_initializer(&char_type.const_array(array_vals.as_slice()));

                    global
                };

                let ll_str_type = self.type_converter.get_struct_type(expr.type_key);
                let ll_str_val = ll_str_type.const_named_struct(&[
                    global.as_basic_value_enum(),
                    self.ctx
                        .i64_type()
                        .const_int(literal.len() as u64, false)
                        .as_basic_value_enum(),
                ]);

                ll_str_val.as_basic_value_enum()
            }

            AExprKind::TupleInit(tuple_init) => {
                let ll_struct_type = self.type_converter.get_struct_type(tuple_init.type_key);
                let ll_field_values: Vec<BasicValueEnum> = tuple_init
                    .values
                    .iter()
                    .map(|v| self.gen_const_expr(v))
                    .collect();

                ll_struct_type
                    .const_named_struct(ll_field_values.as_slice())
                    .as_basic_value_enum()
            }

            AExprKind::ArrayInit(array_init) => {
                let ll_array_type = self.type_converter.get_array_type(array_init.type_key);
                let ll_global_array = self.module.add_global(ll_array_type, None, "const_array");

                // Just return an empty array if there is no element type (this can only happen
                // if the array is actually empty).
                if array_init.maybe_element_type_key.is_none() {
                    return self.ctx.i8_type().const_array(&[]).as_basic_value_enum();
                }

                let ll_element_type = self
                    .type_converter
                    .get_basic_type(array_init.maybe_element_type_key.unwrap());

                // Repeat elements in the array by cloning, if necessary.
                let elements = match &array_init.maybe_repeat_count {
                    Some(count) => {
                        vec![array_init.values.first().unwrap().clone(); *count as usize]
                    }
                    None => array_init.values.clone(),
                };

                let ll_array_value = if ll_element_type.is_pointer_type() {
                    let ll_elements: Vec<PointerValue> = elements
                        .iter()
                        .map(|v| self.gen_const_expr(v).into_pointer_value())
                        .collect();
                    ll_element_type
                        .into_pointer_type()
                        .const_array(ll_elements.as_slice())
                        .as_basic_value_enum()
                } else if ll_element_type.is_int_type() {
                    let ll_elements: Vec<IntValue> = elements
                        .iter()
                        .map(|v| self.gen_const_expr(v).into_int_value())
                        .collect();
                    ll_element_type
                        .into_int_type()
                        .const_array(ll_elements.as_slice())
                        .as_basic_value_enum()
                } else if ll_element_type.is_float_type() {
                    let ll_elements: Vec<FloatValue> = elements
                        .iter()
                        .map(|v| self.gen_const_expr(v).into_float_value())
                        .collect();
                    ll_element_type
                        .into_float_type()
                        .const_array(ll_elements.as_slice())
                        .as_basic_value_enum()
                } else if ll_element_type.is_struct_type() {
                    let ll_elements: Vec<StructValue> = elements
                        .iter()
                        .map(|v| self.gen_const_expr(v).into_struct_value())
                        .collect();
                    ll_element_type
                        .into_struct_type()
                        .const_array(ll_elements.as_slice())
                        .as_basic_value_enum()
                } else if ll_element_type.is_array_type() {
                    let ll_elements: Vec<ArrayValue> = elements
                        .iter()
                        .map(|v| self.gen_const_expr(v).into_array_value())
                        .collect();
                    ll_element_type
                        .into_array_type()
                        .const_array(ll_elements.as_slice())
                        .as_basic_value_enum()
                } else {
                    panic!(
                        "unexpected array element type {}",
                        ll_element_type.to_string()
                    )
                };

                ll_global_array.set_initializer(&ll_array_value);
                ll_global_array.as_basic_value_enum()
            }

            AExprKind::StructInit(struct_init) => {
                let struct_type = self
                    .type_store
                    .must_get(struct_init.type_key)
                    .to_struct_type();
                let ll_struct_type = self.type_converter.get_struct_type(struct_init.type_key);
                let mut ll_field_values = vec![];

                for field in &struct_type.fields {
                    ll_field_values.push(
                        self.gen_const_expr(struct_init.must_get_field_value(field.name.as_str())),
                    )
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
                    ll_field_values.push(self.gen_const_expr(val));
                }

                ll_struct_type
                    .const_named_struct(ll_field_values.as_slice())
                    .as_basic_value_enum()
            }

            AExprKind::TypeCast(left_expr, target_type_key) => self
                .gen_type_cast(left_expr, *target_type_key)
                .as_basic_value_enum(),

            AExprKind::Sizeof(type_key) => self
                .type_converter
                .const_int_size_of_type(*type_key)
                .as_basic_value_enum(),

            AExprKind::MemberAccess(access) => {
                let ll_base_val = self.gen_const_expr(&access.base_expr);
                self.get_member_value(
                    ll_base_val,
                    access.base_expr.type_key,
                    access.member_type_key,
                    access.member_name.as_str(),
                )
            }

            _ => panic!("unexpected const expression {}", expr),
        }
    }

    /// Extracts the value of the given symbol that must represent a constant or the accesses of
    /// some field or subfield on a constant.
    fn const_extract_value(&mut self, symbol: &ASymbol) -> BasicValueEnum<'ctx> {
        // Check if this constant represents an intrinsic value.
        if let Some(ll_intrinsic) = self.maybe_get_intrinsic(symbol) {
            return ll_intrinsic;
        }

        let const_value = &self.must_get_const(symbol.name.as_str()).value.clone();
        self.gen_const_expr(const_value)
    }
}
