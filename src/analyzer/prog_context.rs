use std::collections::{HashMap, HashSet, VecDeque};

use colored::Colorize;

use crate::analyzer::ast::func::{AFn, AFnSig};
use crate::analyzer::ast::program::AProgram;
use crate::analyzer::ast::r#enum::AEnumType;
use crate::analyzer::ast::r#struct::AStructType;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::spec::ASpec;
use crate::analyzer::ast::tuple::ATupleType;
use crate::analyzer::error::{AnalyzeError, AnalyzeResult, ErrorKind};
use crate::analyzer::scope::{Scope, ScopeKind, ScopedSymbol};
use crate::analyzer::type_store::{TypeKey, TypeStore};
use crate::analyzer::warn::AnalyzeWarning;
use crate::lexer::pos::{Locatable, Position};
use crate::parser::r#enum::EnumType;
use crate::parser::r#struct::StructType;
use crate::parser::r#type::Type;
use crate::parser::spec::Spec;

/// Represents the result of semantic analysis on a program.
pub struct ProgramAnalysis {
    pub prog: AProgram,
    pub type_store: TypeStore,
    pub errors: Vec<AnalyzeError>,
    pub warnings: Vec<AnalyzeWarning>,
}

impl ProgramAnalysis {
    pub fn from(ctx: ProgramContext, prog: AProgram) -> ProgramAnalysis {
        // Extract and sort errors and warnings by their location in the source file.
        let mut errors: Vec<(Position, AnalyzeError)> =
            ctx.errors.into_iter().map(|(p, e)| (p, e)).collect();
        errors.sort_by(|(pos1, _), (pos2, _)| pos1.cmp(pos2));

        let mut warnings: Vec<(Position, AnalyzeWarning)> =
            ctx.warnings.into_iter().map(|(p, e)| (p, e)).collect();
        warnings.sort_by(|(pos1, _), (pos2, _)| pos1.cmp(&pos2));

        ProgramAnalysis {
            prog,
            type_store: ctx.type_store,
            errors: errors.into_iter().map(|(_, e)| e).collect(),
            warnings: warnings.into_iter().map(|(_, w)| w.clone()).collect(),
        }
    }
}

pub struct ProgramContext {
    type_store: TypeStore,
    /// Maps primitive type names to their type keys.
    primitive_type_keys: HashMap<String, TypeKey>,
    invalid_type_names: HashSet<String>,

    stack: VecDeque<Scope>,
    fn_scope_indices: Vec<usize>,
    loop_scope_indices: Vec<usize>,

    cur_this_type_key: Option<TypeKey>,

    /// Maps un-analyzed struct names to un-analyzed structs.
    unchecked_struct_types: HashMap<String, StructType>,
    /// Maps un-analyzed enum names to un-analyzed enums.
    unchecked_enum_types: HashMap<String, EnumType>,
    /// Maps un-analyzed specs names to un-analyzed specs.
    unchecked_specs: HashMap<String, Spec>,
    /// Maps function names to analyzed function signatures.
    defined_fn_sigs: HashMap<String, AFnSig>,
    /// Maps function names to analyzed functions.
    funcs: HashMap<String, AFn>,
    /// Maps type keys to mappings from their member function names to their member function
    /// signatures.
    type_member_fn_sigs: HashMap<TypeKey, HashMap<String, AFnSig>>,
    /// Maps spec names to analyzed specs.
    specs: HashMap<String, ASpec>,
    /// Maps struct type name to struct type key.
    struct_type_keys: HashMap<String, TypeKey>,
    /// Maps enum type name to enum type key.
    enum_type_keys: HashMap<String, TypeKey>,
    /// Maps tuple type to tuple type key.
    tuple_type_keys: HashMap<ATupleType, TypeKey>,

    warnings: HashMap<Position, AnalyzeWarning>,
    errors: HashMap<Position, AnalyzeError>,
}

impl ProgramContext {
    pub fn new() -> Self {
        let mut type_store = TypeStore::new();
        let mut primitive_type_keys = HashMap::new();

        for (_, at) in AType::primitives() {
            let name = at.name().to_string();
            let key = type_store.insert(at);
            primitive_type_keys.insert(name, key);
        }

        ProgramContext {
            type_store,
            primitive_type_keys,
            invalid_type_names: Default::default(),
            stack: VecDeque::from([Scope::new(ScopeKind::InlineClosure, vec![], None)]),
            fn_scope_indices: vec![],
            loop_scope_indices: vec![],
            cur_this_type_key: None,
            unchecked_struct_types: Default::default(),
            unchecked_enum_types: Default::default(),
            unchecked_specs: Default::default(),
            defined_fn_sigs: Default::default(),
            funcs: Default::default(),
            type_member_fn_sigs: Default::default(),
            specs: Default::default(),
            struct_type_keys: Default::default(),
            enum_type_keys: Default::default(),
            tuple_type_keys: Default::default(),
            warnings: Default::default(),
            errors: Default::default(),
        }
    }

    fn search_stack_ref<F, R>(&self, visit: F) -> Option<&R>
    where
        F: Fn(&Scope) -> Option<&R>,
    {
        for scope in self.stack.iter().rev() {
            if let Some(result) = visit(scope) {
                return Some(result);
            }
        }

        None
    }

    fn search_stack<F, R>(&self, visit: F) -> Option<R>
    where
        F: Fn(&Scope) -> Option<R>,
    {
        for scope in self.stack.iter().rev() {
            if let Some(result) = visit(scope) {
                return Some(result);
            }
        }

        None
    }

    fn insert_type_key(&mut self, typ: Type, key: TypeKey) {
        self.stack
            .back_mut()
            .unwrap()
            .insert_type_key(typ.clone(), key);
    }

    fn check_type_name_not_used<T: Locatable>(&mut self, name: &str, loc: &T) -> bool {
        if self.primitive_type_keys.contains_key(name)
            || self.unchecked_struct_types.contains_key(name)
            || self.unchecked_enum_types.contains_key(name)
            || self.unchecked_specs.contains_key(name)
        {
            self.insert_err(AnalyzeError::new(
                ErrorKind::DuplicateType,
                format_code!("another type named {} already exists", name).as_str(),
                loc,
            ));

            return false;
        }

        return true;
    }

    pub fn type_store(&self) -> &TypeStore {
        &self.type_store
    }

    pub fn errors(&self) -> &HashMap<Position, AnalyzeError> {
        &self.errors
    }

    #[cfg(test)]
    pub fn warnings(&self) -> &HashMap<Position, AnalyzeWarning> {
        &self.warnings
    }

    pub fn insert_err(&mut self, err: AnalyzeError) {
        self.errors.insert(err.start_pos.clone(), err);
    }

    pub fn insert_warn(&mut self, warn: AnalyzeWarning) {
        self.warnings.insert(warn.start_pos.clone(), warn);
    }

    /// If the given result is an error, consumes and stores the error, returning None. Otherwise,
    /// returns the result.
    pub fn consume_error<T>(&mut self, result: AnalyzeResult<T>) -> Option<T> {
        match result {
            Ok(v) => Some(v),
            Err(e) => {
                self.insert_err(e);
                None
            }
        }
    }

    pub fn insert_type(&mut self, typ: AType) -> TypeKey {
        let (maybe_type_name, is_struct, is_enum, maybe_tuple_type) = match &typ {
            AType::Struct(struct_type) => {
                let maybe_name = match struct_type.name.is_empty() {
                    true => None,
                    false => {
                        if let Some(tk) = self.struct_type_keys.get(struct_type.name.as_str()) {
                            return *tk;
                        }

                        Some(struct_type.name.clone())
                    }
                };

                (maybe_name, true, false, None)
            }

            AType::Enum(enum_type) => {
                let maybe_name = match enum_type.name.is_empty() {
                    true => None,
                    false => {
                        if let Some(tk) = self.enum_type_keys.get(enum_type.name.as_str()) {
                            return *tk;
                        }

                        Some(enum_type.name.clone())
                    }
                };

                (maybe_name, false, true, None)
            }

            AType::Tuple(tuple_type) => {
                // Avoid duplicating tuple types.
                if let Some(existing_tuple_tk) = self.tuple_type_keys.get(tuple_type) {
                    return *existing_tuple_tk;
                }

                (None, false, false, Some(tuple_type.clone()))
            }

            _ => (None, false, false, None),
        };

        let type_key = self.type_store.insert(typ);

        if let Some(name) = maybe_type_name {
            if is_struct {
                self.struct_type_keys.insert(name, type_key);
            } else if is_enum {
                self.enum_type_keys.insert(name, type_key);
            }
        } else if let Some(tuple_type) = maybe_tuple_type {
            self.tuple_type_keys.insert(tuple_type, type_key);
        }

        type_key
    }

    pub fn resolve_type(&mut self, typ: &Type) -> TypeKey {
        if let Type::Unresolved(unresolved_type) = typ {
            if unresolved_type.name == "This" {
                return match self.get_cur_this_type_key() {
                    Some(tk) => tk,
                    None => {
                        self.insert_err(AnalyzeError::new(
                            ErrorKind::UndefType,
                            format_code!(
                                "cannot use type {} outside of {} or {} block",
                                "This",
                                "spec",
                                "impl"
                            )
                            .as_str(),
                            typ,
                        ));

                        self.unknown_type_key()
                    }
                };
            }

            if let Some(key) = self.primitive_type_keys.get(unresolved_type.name.as_str()) {
                return *key;
            }
        }

        if let Some(key) = self.search_stack(|scope| scope.get_type_key(typ)) {
            return key;
        }

        let a_type = AType::from(self, typ);
        let key = self.insert_type(a_type);
        self.insert_type_key(typ.clone(), key);

        key
    }

    pub fn get_type_key_by_type_name(&self, name: &str) -> Option<TypeKey> {
        if let Some(key) = self.primitive_type_keys.get(name) {
            return Some(*key);
        }

        let typ = Type::new_unresolved(name);
        self.search_stack(|scope| scope.get_type_key(&typ))
    }

    pub fn unknown_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("<unknown>").unwrap()
    }

    #[cfg(test)]
    pub fn none_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("<none>").unwrap()
    }

    pub fn bool_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("bool").unwrap()
    }

    pub fn i64_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("i64").unwrap()
    }

    pub fn u64_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("u64").unwrap()
    }

    pub fn str_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("str").unwrap()
    }

    pub fn ptr_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("ptr").unwrap()
    }

    pub fn this_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("This").unwrap()
    }

    pub fn push_scope(&mut self, scope: Scope) {
        match &scope.kind {
            ScopeKind::FnBody => self.fn_scope_indices.push(self.stack.len()),
            ScopeKind::LoopBody => self.loop_scope_indices.push(self.stack.len()),
            _ => {}
        }

        self.stack.push_back(scope);
    }

    pub fn pop_scope(&mut self) -> Scope {
        let scope = self.stack.pop_back().unwrap();

        match &scope.kind {
            ScopeKind::FnBody => {
                self.fn_scope_indices.pop();
            }
            ScopeKind::LoopBody => {
                self.loop_scope_indices.pop();
            }
            _ => {}
        };

        scope
    }

    pub fn must_get_type(&self, type_key: TypeKey) -> &AType {
        self.type_store.must_get(type_key)
    }

    pub fn replace_type(&mut self, type_key: TypeKey, typ: AType) {
        self.type_store.replace(type_key, typ);
    }

    pub fn try_insert_unchecked_struct_type(&mut self, struct_type: StructType) {
        if self.check_type_name_not_used(struct_type.name.as_str(), &struct_type) {
            self.unchecked_struct_types
                .insert(struct_type.name.clone(), struct_type);
        }
    }

    pub fn try_insert_unchecked_enum_type(&mut self, enum_type: EnumType) {
        if self.check_type_name_not_used(enum_type.name.as_str(), &enum_type) {
            self.unchecked_enum_types
                .insert(enum_type.name.clone(), enum_type);
        }
    }

    pub fn try_insert_unchecked_spec(&mut self, spec: Spec) {
        if self.check_type_name_not_used(spec.name.as_str(), &spec) {
            self.unchecked_specs.insert(spec.name.clone(), spec);
        }
    }

    pub fn remove_unchecked_struct_type(&mut self, name: &str) {
        self.unchecked_struct_types.remove(name);
    }

    pub fn remove_unchecked_enum_type(&mut self, name: &str) {
        self.unchecked_enum_types.remove(name);
    }

    pub fn insert_invalid_type_name(&mut self, name: &str) {
        self.invalid_type_names.insert(name.to_string());
    }

    /// Returns true if the given name is the name of a type that has been marked as invalid.
    pub fn is_name_of_invalid_type(&self, name: &str) -> bool {
        self.invalid_type_names.contains(name)
    }

    pub fn insert_defined_fn_sig(&mut self, sig: AFnSig) {
        assert!(self.defined_fn_sigs.insert(sig.name.clone(), sig).is_none());
    }

    pub fn get_defined_fn_sig(&self, name: &str) -> Option<&AFnSig> {
        self.defined_fn_sigs.get(name)
    }

    pub fn set_cur_this_type_key(&mut self, maybe_type_key: Option<TypeKey>) {
        self.cur_this_type_key = maybe_type_key;
    }

    pub fn get_cur_this_type_key(&mut self) -> Option<TypeKey> {
        self.cur_this_type_key
    }

    pub fn get_member_fn(&self, type_key: TypeKey, fn_name: &str) -> Option<&AFnSig> {
        match self.type_member_fn_sigs.get(&type_key) {
            Some(member_fns) => member_fns.get(fn_name),
            None => None,
        }
    }

    pub fn insert_member_fn(&mut self, type_key: TypeKey, member_fn_sig: AFnSig) {
        match self.type_member_fn_sigs.get_mut(&type_key) {
            Some(mem_fns) => {
                mem_fns.insert(member_fn_sig.name.clone(), member_fn_sig);
            }
            None => {
                self.type_member_fn_sigs.insert(
                    type_key,
                    HashMap::from([(member_fn_sig.name.clone(), member_fn_sig)]),
                );
            }
        };
    }

    pub fn get_unchecked_struct_type(&self, name: &str) -> Option<&StructType> {
        self.unchecked_struct_types.get(name)
    }

    pub fn get_unchecked_enum_type(&self, name: &str) -> Option<&EnumType> {
        self.unchecked_enum_types.get(name)
    }

    /// Tries to locate and return the spec with the given name.
    pub fn get_unchecked_spec(&self, name: &str) -> Option<&Spec> {
        self.unchecked_specs.get(name)
    }

    /// Inserts `spec` into the program context.
    pub fn insert_spec(&mut self, spec: ASpec) {
        self.specs.insert(spec.name.clone(), spec);
    }

    /// Tries to locate and return the spec with the given name.
    pub fn get_spec(&self, name: &str) -> Option<&ASpec> {
        self.specs.get(name)
    }

    /// Returns all unchecked struct types in the program context.
    pub fn unchecked_struct_types(&self) -> Vec<&StructType> {
        self.unchecked_struct_types.values().collect()
    }

    /// Returns all unchecked enum types in the program context.
    pub fn unchecked_enum_types(&self) -> Vec<&EnumType> {
        self.unchecked_enum_types.values().collect()
    }

    /// Returns true if the current scope is a function body or exists inside a function body.
    pub fn is_in_fn(&self) -> bool {
        !self.fn_scope_indices.is_empty()
    }

    /// Returns true if the current scope is a loop body or falls within a loop body.
    pub fn is_in_loop(&self) -> bool {
        !self.loop_scope_indices.is_empty()
    }

    /// Adds the symbol type ID to the current scope in the context. If there was already a symbol
    /// with the same name, returns the old symbol.
    pub fn insert_symbol(&mut self, symbol: ScopedSymbol) -> Option<ScopedSymbol> {
        self.stack.back_mut().unwrap().add_symbol(symbol)
    }

    /// Attempts to locate the symbol with the given name and returns it, if found.
    pub fn get_symbol(&self, name: &str) -> Option<&ScopedSymbol> {
        self.search_stack_ref(|scope| scope.get_symbol(name))
    }

    /// Adds the given function to the program context so it can be looked up by full name in the
    /// future. This function should only be used for adding non-templated (non-generic) functions.
    pub fn insert_fn(&mut self, func: AFn) {
        assert!(!func.signature.is_templated());
        self.funcs.insert(func.signature.full_name(), func);
    }

    /// Tries to locate and return the function with the given full name.
    pub fn get_fn(&self, full_name: &str) -> Option<&AFn> {
        self.funcs.get(full_name)
    }

    /// Returns the struct type with the given name.
    pub fn get_struct_type(&self, name: &str) -> Option<&AStructType> {
        if let Some(tk) = self.struct_type_keys.get(name) {
            return Some(self.must_get_type(*tk).to_struct_type());
        }

        None
    }

    /// Returns the struct type with the given name.
    pub fn get_enum_type(&self, name: &str) -> Option<&AEnumType> {
        if let Some(tk) = self.struct_type_keys.get(name) {
            return Some(self.must_get_type(*tk).to_enum_type());
        }

        None
    }

    /// Returns the expected return type key for the current function body scope.
    pub fn get_cur_expected_ret_type_key(&self) -> Option<TypeKey> {
        let fn_scope_index = *self.fn_scope_indices.last().unwrap();
        self.stack.get(fn_scope_index).unwrap().ret_type_key()
    }

    /// Returns a string containing the human-readable version of the type corresponding to the
    /// given type key.
    pub fn display_type_for_key(&self, type_key: TypeKey) -> String {
        self.must_get_type(type_key).display(self)
    }
}
