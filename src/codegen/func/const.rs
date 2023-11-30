use inkwell::values::{
    ArrayValue, BasicValue, BasicValueEnum, IntValue, PointerValue, StructValue,
};

use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::r#type::AType;
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

                self.builder.build_bitcast(
                    global.as_pointer_value(),
                    self.type_converter.get_basic_type(expr.type_key),
                    "str_lit_as_i8_ptr",
                )
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

                if ll_element_type.is_pointer_type() {
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
                }
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
                        self.gen_const_expr(
                            struct_init.field_values.get(field.name.as_str()).unwrap(),
                        ),
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

            AExprKind::TypeCast(left_expr, target_type_key) => {
                let lhs = self.gen_const_expr(left_expr);
                self.gen_type_cast(lhs, *target_type_key)
                    .as_basic_value_enum()
            }

            _ => panic!("unexpected const expression {}", expr),
        }
    }

    /// Extracts the value of the given symbol that must represent a constant or the accesses of
    /// some field or subfield on a constant.
    fn const_extract_value(&mut self, symbol: &ASymbol) -> BasicValueEnum<'ctx> {
        let const_value = &self.must_get_const(symbol.name.as_str()).value.clone();
        let mut ll_const_value = self.gen_const_expr(const_value);

        // If the symbol just refers to some constant by name and has no member access, we can just
        // return the value associated with that constant.
        if symbol.member_access.is_none() {
            return ll_const_value;
        }

        // At this point we know we need to access some member on the constant.
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
