use std::collections::{HashMap, HashSet, VecDeque};

use colored::Colorize;

use crate::analyzer::ast::func::{AFn, AFnSig};
use crate::analyzer::ast::pointer::APointerType;
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
    /// Creates a new program analysis from the given program and program context.
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
    /// Stores all types that are successfully analyzed during semantic analysis.
    type_store: TypeStore,
    /// Maps primitive type names to their type keys.
    primitive_type_keys: HashMap<String, TypeKey>,
    /// Contains the names of all types that have been marked as "invalid" by the analyzer. At the
    /// time of writing this, this should only be used for illegal cyclical types with infinite
    /// size.
    invalid_type_names: HashSet<String>,

    /// Each scope on this stack corresponds to a scope in the program. Each scope will store
    /// information local to only that scope like variables (symbols).
    stack: VecDeque<Scope>,
    /// Tracks the indices of function body scopes so we can locate them easily when searching the
    /// stack.
    fn_scope_indices: Vec<usize>,
    /// Tracks the indices of loop body scopes so we can locate them easily when searching the
    /// stack.
    loop_scope_indices: Vec<usize>,

    /// Will contain the type key corresponding to the current `spec` or `impl` block that is being
    /// analyzed, if any.
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
    pointer_type_keys: HashMap<APointerType, TypeKey>,

    /// Collects warnings emitted by the analyzer during analysis.
    warnings: HashMap<Position, AnalyzeWarning>,
    /// Collects errors emitted by the analyzer during analysis.
    errors: HashMap<Position, AnalyzeError>,
}

impl ProgramContext {
    /// Creates a new program context. The program context will be initialized with stack containing
    /// a single scope representing the global scope and a type store containing primitive types.
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
            pointer_type_keys: Default::default(),
            warnings: Default::default(),
            errors: Default::default(),
        }
    }

    /// Calls `visit` on each scope on the stack starting from the current scope and ending at the
    /// global scope until `visit` returns `Some`.
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

    /// Does the same thing as `search_stack_ref`, except allows `visit` to return an owned value
    /// rather than a reference.
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

    /// Inserts a mapping from `typ` to `key` into the current scope.
    fn insert_type_key(&mut self, typ: Type, key: TypeKey) {
        self.stack
            .back_mut()
            .unwrap()
            .insert_type_key(typ.clone(), key);
    }

    /// Emits an error and returns false if there already exists a type with the given name.
    /// Otherwise, returns true.
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

    /// Returns a reference to the type store.
    pub fn type_store(&self) -> &TypeStore {
        &self.type_store
    }

    /// Returns a mapping from error start position to the error that occurred there.
    pub fn errors(&self) -> &HashMap<Position, AnalyzeError> {
        &self.errors
    }

    /// Returns a mapping from warning start position to the warning that occurred there.
    #[cfg(test)]
    pub fn warnings(&self) -> &HashMap<Position, AnalyzeWarning> {
        &self.warnings
    }

    /// Inserts an error into the program context.
    pub fn insert_err(&mut self, err: AnalyzeError) {
        self.errors.insert(err.start_pos.clone(), err);
    }

    /// Inserts a warning into the program context.
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

    /// Inserts the given analyzed type into the program context. This function will also handle
    /// tracking struct and enum types by name. If another matching struct, enum, or tuple type
    /// already exists, `typ` will not be inserted and the type key for the existing type will be
    /// returned.
    pub fn insert_type(&mut self, typ: AType) -> TypeKey {
        // First, we'll check if this type already exists so we can avoid duplicating it if so.
        let (maybe_type_name, is_struct, is_enum, maybe_tuple_type, maybe_ptr_type) = match &typ {
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

                (maybe_name, true, false, None, None)
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

                (maybe_name, false, true, None, None)
            }

            AType::Tuple(tuple_type) => {
                if let Some(existing_tuple_tk) = self.tuple_type_keys.get(tuple_type) {
                    return *existing_tuple_tk;
                }

                (None, false, false, Some(tuple_type.clone()), None)
            }

            AType::Pointer(ptr_type) => {
                if let Some(existing_ptr_tk) = self.pointer_type_keys.get(ptr_type) {
                    return *existing_ptr_tk;
                }

                (None, false, false, None, Some(ptr_type.clone()))
            }

            _ => (None, false, false, None, None),
        };

        // Store the newly analyzed type.
        let type_key = self.type_store.insert(typ);

        // Create an additional mapping to the new type key to avoid type duplication, if necessary.
        if let Some(name) = maybe_type_name {
            if is_struct {
                self.struct_type_keys.insert(name, type_key);
            } else if is_enum {
                self.enum_type_keys.insert(name, type_key);
            }
        } else if let Some(tuple_type) = maybe_tuple_type {
            self.tuple_type_keys.insert(tuple_type, type_key);
        } else if let Some(ptr_type) = maybe_ptr_type {
            self.pointer_type_keys.insert(ptr_type, type_key);
        }

        type_key
    }

    /// Tries to map the given un-analyzed type to a type key and return that type key. If there is
    /// no existing mapping for `typ`, performs semantic analysis on `typ`, inserts it into the
    /// type store and returns the resulting type key.
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

    /// Tries to locate and return the type key associated with the type with the given name.
    pub fn get_type_key_by_type_name(&self, name: &str) -> Option<TypeKey> {
        if let Some(key) = self.primitive_type_keys.get(name) {
            return Some(*key);
        }

        let typ = Type::new_unresolved(name);
        self.search_stack(|scope| scope.get_type_key(&typ))
    }

    /// Returns the type key for the analyzer-internal `<unknown>` type.
    pub fn unknown_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("<unknown>").unwrap()
    }

    /// Returns the type key for the analyzer-internal `<none>` type.
    #[cfg(test)]
    pub fn none_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("<none>").unwrap()
    }

    /// Returns the type key for the `bool` type.
    pub fn bool_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("bool").unwrap()
    }

    /// Returns the type key for the `i64` type.
    pub fn i64_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("i64").unwrap()
    }

    /// Returns the type key for the `u64` type.
    pub fn u64_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("u64").unwrap()
    }

    /// Returns the type key for the `str` type.
    pub fn str_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("str").unwrap()
    }

    /// Returns the type key for the `rawptr` type.
    pub fn rawptr_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("rawptr").unwrap()
    }

    /// Returns the type key for the special `This` type.
    pub fn this_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("This").unwrap()
    }

    /// Pushes `scope` onto the stack.
    pub fn push_scope(&mut self, scope: Scope) {
        match &scope.kind {
            ScopeKind::FnBody => self.fn_scope_indices.push(self.stack.len()),
            ScopeKind::LoopBody => self.loop_scope_indices.push(self.stack.len()),
            _ => {}
        }

        self.stack.push_back(scope);
    }

    /// Pops and returns the current scope from the stack.
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

    /// Returns the type associated with the given key. Panics if there is no such type.
    pub fn must_get_type(&self, type_key: TypeKey) -> &AType {
        self.type_store.must_get(type_key)
    }

    /// Replaces the existing type associated with `type_key` with `typ`.
    pub fn replace_type(&mut self, type_key: TypeKey, typ: AType) {
        self.type_store.replace(type_key, typ);
    }

    /// Tries to insert the un-analyzed struct type into the program context. Does nothing if the
    /// struct type has a type name that is already used.
    pub fn try_insert_unchecked_struct_type(&mut self, struct_type: StructType) {
        if self.check_type_name_not_used(struct_type.name.as_str(), &struct_type) {
            self.unchecked_struct_types
                .insert(struct_type.name.clone(), struct_type);
        }
    }

    /// Tries to insert the un-analyzed enum type into the program context. Does nothing if the
    /// enum type has a type name that is already used.
    pub fn try_insert_unchecked_enum_type(&mut self, enum_type: EnumType) {
        if self.check_type_name_not_used(enum_type.name.as_str(), &enum_type) {
            self.unchecked_enum_types
                .insert(enum_type.name.clone(), enum_type);
        }
    }

    /// Tries to insert the un-analyzed spec into the program context. Does nothing if the spec
    /// has a name that is already used.
    pub fn try_insert_unchecked_spec(&mut self, spec: Spec) {
        if self.check_type_name_not_used(spec.name.as_str(), &spec) {
            self.unchecked_specs.insert(spec.name.clone(), spec);
        }
    }

    /// Removes the un-analyzed struct type with the given name from the program context.
    pub fn remove_unchecked_struct_type(&mut self, name: &str) {
        self.unchecked_struct_types.remove(name);
    }

    /// Removes the un-analyzed enum type with the given name from the program context.
    pub fn remove_unchecked_enum_type(&mut self, name: &str) {
        self.unchecked_enum_types.remove(name);
    }

    /// Marks the given type name as invalid.
    pub fn insert_invalid_type_name(&mut self, name: &str) {
        self.invalid_type_names.insert(name.to_string());
    }

    /// Returns true if the given name is the name of a type that has been marked as invalid.
    pub fn is_name_of_invalid_type(&self, name: &str) -> bool {
        self.invalid_type_names.contains(name)
    }

    /// Inserts the given function signature into the program context, thereby declaring it as
    /// a defined function. This is done so we can locate function signatures before having
    /// analyzed their bodies.
    pub fn insert_defined_fn_sig(&mut self, sig: AFnSig) {
        assert!(self.defined_fn_sigs.insert(sig.name.clone(), sig).is_none());
    }

    /// Gets the signatures for the function with the given name.
    pub fn get_defined_fn_sig(&self, name: &str) -> Option<&AFnSig> {
        self.defined_fn_sigs.get(name)
    }

    /// Sets the type key associated with the current `impl` or `spec` type so it can be retrieved
    /// during analysis of the `impl` or `spec` body.
    pub fn set_cur_this_type_key(&mut self, maybe_type_key: Option<TypeKey>) {
        self.cur_this_type_key = maybe_type_key;
    }

    /// Returns the type key associated with the current `impl` or `spec` type being analyzed.
    pub fn get_cur_this_type_key(&mut self) -> Option<TypeKey> {
        self.cur_this_type_key
    }

    /// Returns the member function with the given name on the type associated with `type_key`.
    pub fn get_member_fn(&self, type_key: TypeKey, fn_name: &str) -> Option<&AFnSig> {
        match self.type_member_fn_sigs.get(&type_key) {
            Some(member_fns) => member_fns.get(fn_name),
            None => None,
        }
    }

    /// Inserts `member_fn_sig` as a member function on the type that corresponds to `type_key`.
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

    /// Returns the un-analyzed struct type with the given name.
    pub fn get_unchecked_struct_type(&self, name: &str) -> Option<&StructType> {
        self.unchecked_struct_types.get(name)
    }

    /// Returns the un-analyzed enum type with the given name.
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

    /// Adds the symbol type key to the current scope in the context. If there was already a symbol
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
