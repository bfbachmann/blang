use inkwell::values::{BasicValue, BasicValueEnum, PointerValue};

use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::symbol::{AMemberAccess, ASymbol};
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
        let ll_var_ptr = self.get_var_ptr(&assign.symbol);

        // Most primitive values can be assigned (i.e. copied) with a store instruction. Composite
        // values like structs need to be copied differently.
        self.copy_value(ll_expr_val, ll_var_ptr, assign.val.type_key);
    }

    /// Gets a pointer to the given variable or member.
    pub(crate) fn get_var_ptr(&mut self, var: &ASymbol) -> PointerValue<'ctx> {
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
    pub(crate) fn is_var_module_fn(&self, var: &ASymbol) -> bool {
        if var.member_access.is_some() {
            false
        } else {
            self.module.get_function(var.name.as_str()).is_some()
        }
    }

    /// Gets a variable (or member) and returns its value.
    pub(crate) fn get_var_value(&mut self, var: &ASymbol) -> BasicValueEnum<'ctx> {
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
}
