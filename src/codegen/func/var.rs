use inkwell::values::{BasicValue, BasicValueEnum, PointerValue};

use crate::analyzer::ast::expr::{AExpr, AExprKind};
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::symbol::ASymbol;
use crate::analyzer::ast::var_assign::AVarAssign;
use crate::analyzer::type_store::TypeKey;

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
        let ll_dst_ptr = self.create_entry_alloc(name, type_key, ll_val);
        self.copy_value(ll_val, ll_dst_ptr, type_key);
        self.vars.insert(name.to_string(), ll_dst_ptr);
        ll_dst_ptr
    }

    /// Assigns the value to the variable with the given name. Panics if no such variable exists.
    pub(crate) fn assign_var(&mut self, assign: &AVarAssign) {
        // Compile the expression value being assigned.
        let ll_expr_val = self.gen_expr(&assign.val);

        // Get a pointer to the target variable (or variable member).
        let ll_var_ptr = self.get_ptr_to(&assign.target);

        // Most primitive values can be assigned (i.e. copied) with a store instruction. Composite
        // values like structs need to be copied differently.
        self.copy_value(ll_expr_val, ll_var_ptr, assign.val.type_key);
    }

    /// Returns a pointer to the address in which the given value is stored.
    pub(crate) fn get_ptr_to(&mut self, value: &AExpr) -> PointerValue<'ctx> {
        match &value.kind {
            AExprKind::Symbol(symbol) => self.get_var_ptr_by_name(symbol.name.as_str()),
            AExprKind::MemberAccess(access) => {
                let ll_base_ptr = self.get_ptr_to(&access.base_expr);
                self.get_member_ptr(
                    ll_base_ptr.as_basic_value_enum(),
                    access.base_expr.type_key,
                    access.member_name.as_str(),
                )
            }
            other => panic!("cannot get pointer to expression {}", other),
        }
    }

    /// Gets a pointer to the given variable or member.
    pub(crate) fn get_var_ptr(&mut self, var: &ASymbol) -> PointerValue<'ctx> {
        self.get_var_ptr_by_name(var.name.as_str())
    }

    /// Returns true if `var` refers directly to a function in this module. Note that this function
    /// will return false if `var` is has a function type, but refers to a local variable rather
    /// than a function defined within this module.
    pub(crate) fn is_var_module_fn(&self, var: &ASymbol) -> bool {
        self.module.get_function(var.name.as_str()).is_some()
    }

    /// Gets a variable (or member) and returns its value.
    pub(crate) fn get_var_value(&mut self, var: &ASymbol) -> BasicValueEnum<'ctx> {
        // Get a pointer to the variable or member.
        let ll_var_ptr = self.get_var_ptr(var);

        // Load the value from the pointer (unless it's a composite value that is passed with
        // pointers, or a pointer to a module-level function).
        let var_type = self.type_store.must_get(var.type_key);
        if var_type.is_composite() || self.is_var_module_fn(var) {
            ll_var_ptr.as_basic_value_enum()
        } else {
            let ll_var_type = self.type_converter.get_basic_type(var.type_key);
            self.builder
                .build_load(ll_var_type, ll_var_ptr, var.name.as_str())
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

    /// Returns a pointer to the member with name `member_name` on `ll_base_val`.
    pub(crate) fn get_member_ptr(
        &mut self,
        ll_base_val: BasicValueEnum<'ctx>,
        base_expr_type_key: TypeKey,
        member_name: &str,
    ) -> PointerValue<'ctx> {
        let base_expr_type = self.type_store.must_get(base_expr_type_key);
        let ll_base_expr_type = self.type_converter.get_basic_type(base_expr_type_key);

        match base_expr_type {
            AType::Struct(struct_type) => {
                // Get a pointer to the struct field at the computed index.
                self.builder
                    .build_struct_gep(
                        ll_base_expr_type,
                        ll_base_val.into_pointer_value(),
                        struct_type.get_field_index(member_name).unwrap() as u32,
                        format!("{}_ptr", member_name).as_str(),
                    )
                    .unwrap()
            }

            AType::Tuple(tuple_type) => {
                // Get a pointer to the tuple field at the computed index.
                self.builder
                    .build_struct_gep(
                        ll_base_expr_type,
                        ll_base_val.into_pointer_value(),
                        tuple_type.get_field_index(member_name) as u32,
                        format!("{}_ptr", member_name).as_str(),
                    )
                    .unwrap()
            }

            other => panic!("invalid member access on type {}", other),
        }
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
            let ll_member_type = self.type_converter.get_basic_type(member_type_key);
            return self
                .builder
                .build_load(ll_member_type, ll_member_ptr, member_name);
        }

        // At this point we know that we're accessing a member on a constant.
        let base_expr_type = self.type_store.must_get(base_expr_type_key);
        match base_expr_type {
            AType::Struct(struct_type) => {
                // Get the value of the struct field at the computed index.
                self.builder
                    .build_extract_value(
                        ll_base_val.into_struct_value(),
                        struct_type.get_field_index(member_name).unwrap() as u32,
                        format!("{}_ptr", member_name).as_str(),
                    )
                    .unwrap()
            }

            AType::Tuple(tuple_type) => {
                // Get the value of the tuple field at the computed index.
                self.builder
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
