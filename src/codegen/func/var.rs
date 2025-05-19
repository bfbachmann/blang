use inkwell::values::{BasicValue, BasicValueEnum, PointerValue};

use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::symbol::{ASymbol, SymbolKind};
use crate::analyzer::ast::var_assign::AVarAssign;
use crate::analyzer::mangling::mangle_name;
use crate::analyzer::type_store::{GetType, TypeKey};
use crate::lexer::pos::Locatable;
use crate::parser::ast::op::Operator;

use super::FnCodeGen;

impl<'a, 'ctx> FnCodeGen<'a, 'ctx> {
    /// Allocates space on the stack for a new variable of the type corresponding to `type_key` and
    /// writes `ll_val` to the allocated memory. Also stores a pointer to the allocated memory in
    /// `self.vars` with `name`. Returns a pointer to the new variable.
    pub(crate) fn create_var(
        &mut self,
        name: &str,
        type_key: TypeKey,
        ll_val: BasicValueEnum<'ctx>,
    ) -> PointerValue<'ctx> {
        let ll_dst_ptr = self.stack_alloc(name, type_key);
        self.copy_value(ll_val, ll_dst_ptr, type_key);
        self.insert_var(name.to_string(), ll_dst_ptr);
        ll_dst_ptr
    }

    /// Assigns the value to the variable with the given name. Panics if no such variable exists.
    pub(crate) fn assign_var(&mut self, assign: &AVarAssign) {
        self.set_di_location(&assign.target.span().start_pos);

        // Get a pointer to the target variable (or variable member).
        let ll_var_ptr = self.get_ptr_to(&assign.target);

        // Compile the expression value being assigned.
        let ll_expr_val = self.gen_expr(&assign.val);

        // Most primitive values can be assigned (i.e. copied) with a store instruction. Composite
        // values like structs need to be copied differently.
        self.copy_value(ll_expr_val, ll_var_ptr, assign.val.type_key);
    }

    /// Returns a pointer to the address in which the given value is stored.
    pub(crate) fn get_ptr_to(&mut self, value: &AExpr) -> PointerValue<'ctx> {
        match &value.kind {
            AExprKind::Symbol(symbol) => self.get_var_ptr(symbol),

            AExprKind::MemberAccess(access) => {
                let ll_base_ptr = self.get_ptr_to(&access.base_expr);
                self.get_member_ptr(
                    ll_base_ptr.as_basic_value_enum(),
                    access.base_expr.type_key,
                    access.member_name.as_str(),
                )
            }

            AExprKind::Index(index) => {
                let ll_collection_ptr = self.get_ptr_to(&index.collection_expr);
                let ll_index_val = self.gen_expr(&index.index_expr);
                let collection_type = self.type_converter.get_type(index.collection_expr.type_key);

                if collection_type.is_tuple() {
                    // Handle tuple indexing the same way we handle struct member access
                    // because tuples are just structs.
                    self.get_member_ptr(
                        ll_collection_ptr.as_basic_value_enum(),
                        index.collection_expr.type_key,
                        ll_index_val
                            .into_int_value()
                            .get_zero_extended_constant()
                            .unwrap()
                            .to_string()
                            .as_str(),
                    )
                } else {
                    // At this point we know we're indexing an array.
                    let ll_array_type = self
                        .type_converter
                        .get_array_type(index.collection_expr.type_key);
                    unsafe {
                        self.ll_builder
                            .build_in_bounds_gep(
                                ll_array_type,
                                ll_collection_ptr,
                                &[
                                    self.ll_ctx.i32_type().const_int(0, false),
                                    ll_index_val.into_int_value(),
                                ],
                                "elem_ptr",
                            )
                            .unwrap()
                    }
                }
            }

            AExprKind::UnaryOperation(Operator::Defererence, expr) => {
                self.gen_expr(expr).into_pointer_value()
            }

            other => panic!("cannot get pointer to expression {}", other),
        }
    }

    /// Gets a pointer to the given variable or member.
    pub(crate) fn get_var_ptr(&mut self, symbol: &ASymbol) -> PointerValue<'ctx> {
        let maybe_mod_id = &symbol.maybe_mod_id;
        let name = symbol.name.as_str();

        match (&symbol.kind, maybe_mod_id) {
            (SymbolKind::Const, Some(mod_id)) => {
                if let Some(consts) = self.mod_consts.get(mod_id) {
                    if let Some(const_) = consts.get(name) {
                        let ll_ptr = self.stack_alloc(name, const_.type_key);
                        let ll_val = self.gen_const_expr(&const_);
                        self.copy_value(ll_val, ll_ptr, const_.type_key);
                        return ll_ptr;
                    }
                }
            }

            (SymbolKind::Static, Some(mod_id)) => {
                if let Some(statics) = self.mod_statics.get(mod_id) {
                    if let Some(static_) = statics.get(name) {
                        let mangled_name = mangle_name(&symbol.name, *mod_id);

                        let ll_global = match self.ll_mod.get_global(&mangled_name) {
                            Some(g) => g,
                            None => {
                                let ll_type = self.type_converter.get_basic_type(static_.type_key);
                                let ll_global =
                                    self.ll_mod.add_global(ll_type, None, &mangled_name);
                                ll_global.set_initializer(
                                    &self.gen_const_expr(static_).as_basic_value_enum(),
                                );
                                ll_global
                            }
                        };

                        return ll_global.as_pointer_value();
                    }
                }
            }

            (SymbolKind::Variable, _) => {
                if let Some(ll_var_ptr) = self.get_var(name) {
                    return *ll_var_ptr;
                }
            }

            (SymbolKind::Fn, _) => {
                return self
                    .get_or_define_function(symbol.type_key)
                    .as_global_value()
                    .as_pointer_value();
            }

            _ => {}
        }

        panic!("failed to resolve variable {}", name);
    }

    /// Gets a variable (or member) and returns its value.
    pub(crate) fn get_var_value(&mut self, var: &ASymbol) -> BasicValueEnum<'ctx> {
        // Check if the symbol actually represents an intrinsic.
        if let Some(ll_intrinsic) = self.maybe_get_intrinsic(var) {
            return ll_intrinsic;
        }

        // Get a pointer to the variable or member.
        let ll_var_ptr = self.get_var_ptr(var);

        // Load the value from the pointer (unless it's a composite value that is passed with
        // pointers, or a pointer to a module-level function).
        if var.kind == SymbolKind::Fn {
            ll_var_ptr.as_basic_value_enum()
        } else {
            self.load_if_basic(ll_var_ptr, var.type_key, var.name.as_str())
        }
    }

    /// If `symbol` represents an intrinsic value, returns the corresponding LLVM
    /// value for that intrinsic. Otherwise, returns `None`.
    pub(crate) fn maybe_get_intrinsic(&mut self, symbol: &ASymbol) -> Option<BasicValueEnum<'ctx>> {
        if symbol.is_null_intrinsic() {
            let ll_type = self.type_converter.get_basic_type(symbol.type_key);
            return Some(
                ll_type
                    .into_pointer_type()
                    .const_null()
                    .as_basic_value_enum(),
            );
        }

        None
    }

    /// Returns a pointer to the member with name `member_name` on `ll_base_val`.
    pub(crate) fn get_member_ptr(
        &mut self,
        ll_base_val: BasicValueEnum<'ctx>,
        base_expr_type_key: TypeKey,
        member_name: &str,
    ) -> PointerValue<'ctx> {
        let base_expr_type = self.type_store.get_type(base_expr_type_key);
        let ll_base_expr_type = self.type_converter.get_basic_type(base_expr_type_key);
        let ll_field_index = match base_expr_type {
            AType::Struct(struct_type) => struct_type.get_field_index(member_name).unwrap() as u32,
            AType::Tuple(tuple_type) => tuple_type.get_field_index(member_name) as u32,
            other => panic!("invalid member access on type {}", other),
        };

        self.ll_builder
            .build_struct_gep(
                ll_base_expr_type,
                ll_base_val.into_pointer_value(),
                ll_field_index,
                format!("{}_ptr", member_name).as_str(),
            )
            .unwrap()
    }

    /// Returns the value of the member with name `member_name` on `ll_base_val`.
    pub(crate) fn get_member_value(
        &mut self,
        ll_base_val: BasicValueEnum<'ctx>,
        base_expr_type_key: TypeKey,
        member_type_key: TypeKey,
        member_name: &str,
    ) -> BasicValueEnum<'ctx> {
        // Handle the case where the value we're accessing is a pointer.
        if ll_base_val.is_pointer_value() {
            let ll_member_ptr = self.get_member_ptr(ll_base_val, base_expr_type_key, member_name);
            return self.load_if_basic(ll_member_ptr, member_type_key, member_name);
        }

        // At this point we know that we're accessing a member on a constant.
        let base_expr_type = self.type_store.get_type(base_expr_type_key);
        match base_expr_type {
            AType::Struct(struct_type) => {
                // Get the value of the struct field at the computed index.
                self.ll_builder
                    .build_extract_value(
                        ll_base_val.into_struct_value(),
                        struct_type.get_field_index(member_name).unwrap() as u32,
                        format!("{}_ptr", member_name).as_str(),
                    )
                    .unwrap()
            }

            AType::Tuple(tuple_type) => {
                // Get the value of the tuple field at the computed index.
                self.ll_builder
                    .build_extract_value(
                        ll_base_val.into_struct_value(),
                        tuple_type.get_field_index(member_name) as u32,
                        format!("{}_ptr", member_name).as_str(),
                    )
                    .unwrap()
            }

            other => panic!("invalid member access on type {}", other),
        }
    }
}
