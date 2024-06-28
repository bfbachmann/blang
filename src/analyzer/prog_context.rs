use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{Hash, Hasher};

use crate::analyzer::ast::array::AArrayType;
use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::func::{AFn, AFnSig};
use crate::analyzer::ast::generic::AGenericType;
use crate::analyzer::ast::params::{AParam, AParams};
use crate::analyzer::ast::pointer::APointerType;
use crate::analyzer::ast::r#enum::AEnumType;
use crate::analyzer::ast::r#struct::AStructType;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::spec::ASpecType;
use crate::analyzer::ast::symbol::ASymbol;
use crate::analyzer::ast::tuple::ATupleType;
use crate::analyzer::error::{AnalyzeError, AnalyzeResult, ErrorKind};
use crate::analyzer::scope::{Scope, ScopeKind, ScopedSymbol};
use crate::analyzer::type_store::{TypeKey, TypeStore};
use crate::analyzer::warn::AnalyzeWarning;
use crate::fmt::{format_code_vec, vec_to_string};
use crate::lexer::pos::{Locatable, Position, Span};
use crate::parser::ast::r#const::Const;
use crate::parser::ast::r#enum::EnumType;
use crate::parser::ast::r#struct::StructType;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::spec::Spec;
use crate::parser::module::Module;

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct ReplacedParam {
    pub param_type_key: TypeKey,
    pub replacement_type_key: TypeKey,
}

/// Represents a polymorphic type that was monomorphized, and the set of
/// parameters that were used to monomorphize it.
#[derive(Debug, Clone, Eq)]
pub struct Monomorphization {
    pub poly_type_key: TypeKey,
    pub mono_type_key: TypeKey,
    pub replaced_params: Vec<ReplacedParam>,
}

impl PartialEq for Monomorphization {
    fn eq(&self, other: &Self) -> bool {
        self.poly_type_key == other.poly_type_key && self.replaced_params == other.replaced_params
    }
}

impl Hash for Monomorphization {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.poly_type_key.hash(state);
        self.replaced_params.hash(state);
    }
}

/// Stores information about code in a given module.
struct ModuleContext {
    /// Each scope on this stack corresponds to a scope in the program. Each scope will store
    /// information local to only that scope like variables (symbols).
    stack: VecDeque<Scope>,
    /// Tracks the indices of function body scopes so we can locate them easily when searching the
    /// stack.
    fn_scope_indices: Vec<usize>,
    /// Tracks the indices of `from` scopes so we can locate them easily when searching the stack.
    from_scope_indices: Vec<usize>,
    /// Tracks the indices of loop body scopes so we can locate them easily when searching the
    /// stack.
    loop_scope_indices: Vec<usize>,

    /// Will contain the type key corresponding to the current `spec` or `impl` block that is being
    /// analyzed, if any.
    cur_self_type_key: Option<TypeKey>,
    /// Maps module name to full module path for each module that was imported into this
    /// module. For example, if an import was specified with `use "my_project/my_mod.bl"`, then
    /// this map would contain the mapping `"my_mod": "my_project/my_mod.bl"`.
    imported_mod_paths: HashMap<String, String>,

    /// The names of public constants defined in this module.
    pub_const_names: HashSet<String>,
    /// The names of public functions defined in this module.
    pub_fn_names: HashSet<String>,
    /// The names of public types defined in this module.
    pub_type_names: HashSet<String>,
    /// The names of public type member functions in this module.
    pub_type_member_fn_names: HashMap<TypeKey, String>,

    /// Contains the names of all types that have been marked as "invalid" by the analyzer. At the
    /// time of writing this, this should only be used for illegal cyclical types with infinite
    /// size.
    invalid_type_names: HashSet<String>,
    /// Maps un-analyzed struct names to un-analyzed structs.
    unchecked_struct_types: HashMap<String, StructType>,
    /// Maps un-analyzed enum names to un-analyzed enums.
    unchecked_enum_types: HashMap<String, EnumType>,
    /// Maps un-analyzed specs names to un-analyzed specs.
    unchecked_specs: HashMap<String, Spec>,
    /// Maps constant names to un-analyzed constant values.
    unchecked_consts: HashMap<String, Const>,
    /// Maps function names to analyzed function signatures.
    defined_fn_sigs: HashMap<String, AFnSig>,
    /// Maps function names to analyzed functions.
    funcs: HashMap<String, AFn>,
    /// Maps constant names to their values.
    const_values: HashMap<String, AExpr>,
    /// Maps struct type name to struct type key.
    struct_type_keys: HashMap<String, TypeKey>,
    /// Maps spec type name to spec type key.
    spec_type_keys: HashMap<String, TypeKey>,
    /// Maps enum type name to enum type key.
    enum_type_keys: HashMap<String, TypeKey>,
}

impl ModuleContext {
    /// Creates a new empty module context.
    fn new() -> ModuleContext {
        ModuleContext {
            stack: VecDeque::from([Scope::new(ScopeKind::InlineClosure, vec![], None)]),
            fn_scope_indices: vec![],
            from_scope_indices: vec![],
            loop_scope_indices: vec![],
            cur_self_type_key: None,
            imported_mod_paths: Default::default(),
            pub_const_names: Default::default(),
            pub_fn_names: Default::default(),
            pub_type_names: Default::default(),
            pub_type_member_fn_names: Default::default(),
            invalid_type_names: Default::default(),
            unchecked_struct_types: Default::default(),
            unchecked_enum_types: Default::default(),
            unchecked_specs: Default::default(),
            unchecked_consts: Default::default(),
            defined_fn_sigs: Default::default(),
            funcs: Default::default(),
            const_values: Default::default(),
            struct_type_keys: Default::default(),
            spec_type_keys: Default::default(),
            enum_type_keys: Default::default(),
        }
    }

    /// Calls `visit` on each scope on the stack of the module starting
    /// from the current scope and ending at the global scope until `visit` returns `Some`.
    /// If `cross_fn_boundaries` is true, the `visit` function will be called with scopes
    /// that belong to other functions that the current function falls within. Otherwise,
    /// only scopes that fall under the current function and the top-level scope will be visited.
    /// `cross_fn_boundaries` only exists as a means of preventing a function that is declared
    /// inside another function from finding values that were declared inside its parent.
    fn search_stack_ref<F, R>(&self, visit: F, cross_fn_boundaries: bool) -> Option<&R>
    where
        F: Fn(&Scope) -> Option<&R>,
    {
        for scope in self.stack.iter().rev() {
            if let Some(result) = visit(scope) {
                return Some(result);
            }

            // If we're not allowed to cross function boundaries (i.e. if we're
            // not allowed to visit scopes that belong to other functions in
            // which the current function is nested), then just break and visit
            // the outermost (top-level) scope.
            if !cross_fn_boundaries && matches!(scope.kind, ScopeKind::FnBody(_)) {
                break;
            }
        }

        visit(self.stack.front().unwrap())
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
}

/// Stores information about the program for reference during semantic analysis.
pub struct ProgramContext {
    /// Stores all types that are successfully analyzed during semantic analysis.
    pub type_store: TypeStore,
    /// Maps polymorphic type keys to their monomorphizations.
    pub monomorphized_types: HashMap<TypeKey, HashSet<Monomorphization>>,
    /// Maps monomorphic type keys to the monomorphizations that were used to derive them.
    pub type_monomorphizations: HashMap<TypeKey, Monomorphization>,
    /// Maps primitive type names to their type keys.
    primitive_type_keys: HashMap<String, TypeKey>,

    /// The path of the module that is currently being analyzed.
    cur_mod_path: String,

    /// Maps module path to its context.
    module_contexts: HashMap<String, ModuleContext>,

    /// Maps tuple type to tuple type key.
    tuple_type_keys: HashMap<ATupleType, TypeKey>,
    /// Maps array type to array type key.
    array_type_keys: HashMap<AArrayType, TypeKey>,
    /// Maps pointer type to pointer type key.
    pointer_type_keys: HashMap<APointerType, TypeKey>,
    /// Maps generic type to generic type key.
    generic_type_keys: HashMap<AGenericType, TypeKey>,
    /// Maps function types to their type keys.
    fn_type_keys: HashMap<AFnSig, TypeKey>,
    /// Maps type keys to mappings from their member function names to their member function
    /// signatures.
    type_member_fn_sigs: HashMap<TypeKey, HashMap<String, AFnSig>>,
    /// Maps type keys to sets of public member function names for those types.
    /// This is just used to figure out whether a given type member function
    /// was declared public.
    pub_member_fn_names: HashMap<TypeKey, HashSet<String>>,
    /// Maps struct type key to the set of public field names on that struct type.
    pub_struct_field_names: HashMap<TypeKey, HashSet<String>>,
    /// Maps type keys to the paths of the modules in which the types are declared.
    type_declaration_mods: HashMap<TypeKey, String>,
    /// Maps type key to the set of specs implemented by that type.
    spec_impls: HashMap<TypeKey, HashSet<TypeKey>>,
    /// Represents a stack of parameters that are relevant when analyzing parameterized
    /// functions and types.
    params: Vec<AParams>,

    /// Collects warnings emitted by the analyzer during analysis.
    pub warnings: HashMap<Position, AnalyzeWarning>,
    /// Collects errors emitted by the analyzer during analysis.
    pub errors: HashMap<Position, AnalyzeError>,
}

impl ProgramContext {
    /// Creates a new program context. The program context will be initialized with stack containing
    /// a single scope representing the global scope and a type store containing primitive types.
    pub fn new(target_ptr_width: u8, root_mod_path: &str, mod_paths: Vec<&str>) -> Self {
        let mut type_store = TypeStore::new(target_ptr_width);

        // Set up primitive type keys.
        let mut primitive_type_keys = HashMap::new();
        for typ in AType::primitives() {
            let name = typ.name().to_string();
            let key = type_store.insert(typ);
            primitive_type_keys.insert(name, key);
        }

        // Initialize empty module contexts.
        let mut mod_ctxs = HashMap::with_capacity(mod_paths.len());
        for mod_path in &mod_paths {
            mod_ctxs.insert(mod_path.to_string(), ModuleContext::new());
        }

        ProgramContext {
            type_store,
            primitive_type_keys,
            cur_mod_path: root_mod_path.to_string(),
            module_contexts: mod_ctxs,
            tuple_type_keys: Default::default(),
            array_type_keys: Default::default(),
            pointer_type_keys: Default::default(),
            generic_type_keys: Default::default(),
            fn_type_keys: Default::default(),
            type_member_fn_sigs: Default::default(),
            pub_member_fn_names: Default::default(),
            pub_struct_field_names: Default::default(),
            type_declaration_mods: Default::default(),
            spec_impls: Default::default(),
            params: vec![],
            monomorphized_types: Default::default(),
            type_monomorphizations: Default::default(),
            warnings: Default::default(),
            errors: Default::default(),
        }
    }

    /// Creates a new program context where the pointer width is set according to the
    /// host system.
    pub fn new_with_host_ptr_width(root_mod_path: &str, mod_paths: Vec<&str>) -> ProgramContext {
        ProgramContext::new(
            target_lexicon::Triple::host()
                .pointer_width()
                .unwrap()
                .bits(),
            root_mod_path,
            mod_paths,
        )
    }

    /// Returns true only if the module name refers to a valid imported module.
    /// Otherwise, records an error and returns false.
    pub fn check_mod_name<T: Locatable>(&mut self, mod_name: &String, loc: &T) -> bool {
        let mod_ctx = self.cur_mod_ctx();
        match mod_ctx.imported_mod_paths.contains_key(mod_name) {
            true => true,
            false => {
                self.insert_err(AnalyzeError::new(
                    ErrorKind::UndefMod,
                    format_code!("module {} is not defined", mod_name).as_str(),
                    loc,
                ));

                false
            }
        }
    }

    /// Returns the module context corresponding to the module that is currently
    /// being analysed.
    fn cur_mod_ctx(&self) -> &ModuleContext {
        self.module_contexts
            .get(self.cur_mod_path.as_str())
            .unwrap()
    }

    /// Returns the mutable module context corresponding to the module that is
    /// currently being analysed.
    fn cur_mod_ctx_mut(&mut self) -> &mut ModuleContext {
        self.module_contexts
            .get_mut(self.cur_mod_path.as_str())
            .unwrap()
    }

    /// If `maybe_mod_name` is `Some`, returns the corresponding module context.
    /// Otherwise, returns the current module context.
    fn get_mod_ctx(&self, maybe_mod_name: Option<&String>) -> &ModuleContext {
        let mod_ctx = self.cur_mod_ctx();
        match maybe_mod_name {
            Some(mod_name) => {
                let mod_path = mod_ctx.imported_mod_paths.get(mod_name).unwrap();
                self.module_contexts.get(mod_path).unwrap()
            }

            None => mod_ctx,
        }
    }

    /// Inserts a mapping from `typ` to `key` into the current scope.
    fn insert_type_key(&mut self, typ: Type, key: TypeKey) {
        self.cur_mod_ctx_mut()
            .stack
            .back_mut()
            .unwrap()
            .insert_type_key(typ, key);
    }

    /// Emits an error and returns false if there already exists a type with the
    /// given name in the current module.
    /// Otherwise, returns true.
    fn check_type_name_not_used<T: Locatable>(&mut self, name: &str, loc: &T) -> bool {
        let mod_ctx = self.cur_mod_ctx();
        if self.primitive_type_keys.contains_key(name)
            || mod_ctx.unchecked_struct_types.contains_key(name)
            || mod_ctx.unchecked_enum_types.contains_key(name)
            || mod_ctx.unchecked_specs.contains_key(name)
            || self.is_reserved_type_name(name)
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

    /// Returns true if `name` is a reserved type name that cannot be used by users.
    fn is_reserved_type_name(&self, name: &str) -> bool {
        name == "Clone" && !self.cur_mod_path.ends_with("std/specs/clone.bl")
    }

    /// Checks that the given type implements the set of specs on the given
    /// generic type. Returns type keys for specs not implemented by the type.
    pub fn get_missing_spec_impls(
        &self,
        type_key: TypeKey,
        generic_type_key: TypeKey,
    ) -> Vec<TypeKey> {
        let mut missing_spec_type_keys = vec![];
        let spec_type_keys = &self
            .must_get_type(generic_type_key)
            .to_generic_type()
            .spec_type_keys;

        for spec_type_key in spec_type_keys {
            if self.must_get_type(*spec_type_key).to_spec_type().name == "Clone"
                && self.must_get_type(type_key).is_primitive()
            {
                continue;
            }

            let type_implements_spec = self
                .spec_impls
                .get(&type_key)
                .is_some_and(|spec_set| spec_set.contains(spec_type_key));
            if !type_implements_spec {
                missing_spec_type_keys.push(*spec_type_key);
            }
        }

        missing_spec_type_keys
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
        self.errors.insert(err.span.start_pos, err);
    }

    /// Inserts a warning into the program context.
    pub fn insert_warn(&mut self, warn: AnalyzeWarning) {
        self.warnings.insert(warn.span.start_pos, warn);
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

    /// Tries to locate the type key associated with the given type and returns it
    /// if found.
    fn get_existing_type_key(&self, typ: &AType) -> Option<TypeKey> {
        match &typ {
            AType::Bool => return Some(self.bool_type_key()),
            AType::U8 => return Some(self.u8_type_key()),
            AType::I8 => return Some(self.i8_type_key()),
            AType::U32 => return Some(self.u32_type_key()),
            AType::I32 => return Some(self.i32_type_key()),
            AType::F32 => return Some(self.f32_type_key()),
            AType::I64 => return Some(self.i64_type_key()),
            AType::U64 => return Some(self.u64_type_key()),
            AType::F64 => return Some(self.f64_type_key()),
            AType::Int => return Some(self.int_type_key()),
            AType::Uint => return Some(self.uint_type_key()),
            AType::Str => return Some(self.str_type_key()),

            AType::Struct(struct_type) if !struct_type.name.is_empty() => {
                if let Some(tk) = self
                    .cur_mod_ctx()
                    .struct_type_keys
                    .get(struct_type.mangled_name.as_str())
                {
                    return Some(*tk);
                }
            }

            AType::Enum(enum_type) if !enum_type.name.is_empty() => {
                if let Some(tk) = self
                    .cur_mod_ctx()
                    .enum_type_keys
                    .get(enum_type.mangled_name.as_str())
                {
                    return Some(*tk);
                }
            }

            AType::Tuple(tuple_type) => {
                if let Some(existing_tuple_tk) = self.tuple_type_keys.get(tuple_type) {
                    return Some(*existing_tuple_tk);
                }
            }

            AType::Array(array_type) => {
                if let Some(existing_array_tk) = self.array_type_keys.get(array_type) {
                    return Some(*existing_array_tk);
                }
            }

            AType::Function(fn_type) => {
                if let Some(existing_fn_tk) = self.fn_type_keys.get(fn_type.as_ref()) {
                    return Some(*existing_fn_tk);
                }
            }

            AType::Pointer(ptr_type) => {
                if let Some(existing_ptr_tk) = self.pointer_type_keys.get(ptr_type) {
                    return Some(*existing_ptr_tk);
                }
            }

            AType::Spec(spec_type) => {
                if let Some(tk) = self
                    .cur_mod_ctx()
                    .spec_type_keys
                    .get(spec_type.name.as_str())
                {
                    return Some(*tk);
                }
            }

            AType::Generic(generic_type) => {
                if let Some(tk) = self.generic_type_keys.get(generic_type) {
                    return Some(*tk);
                }
            }

            _ => {}
        }

        None
    }

    /// Inserts the given analyzed type into the program context. This function will also handle
    /// tracking named types. The type will be inserted regardless of whether there is
    /// already a matching type in the type store.
    pub fn force_insert_type(&mut self, typ: AType) -> TypeKey {
        // Store the newly analyzed type.
        let type_key = self.type_store.insert(typ);

        // Create an additional mapping to the new type key to avoid type duplication, if necessary.
        let typ = self.must_get_type(type_key);
        let maybe_mangled_type_name = match typ {
            AType::Struct(struct_type) => {
                let mangled_name = struct_type.mangled_name.clone();
                self.cur_mod_ctx_mut()
                    .struct_type_keys
                    .insert(mangled_name.clone(), type_key);
                Some(mangled_name)
            }

            AType::Enum(enum_type) => {
                let mangled_name = enum_type.mangled_name.clone();
                self.cur_mod_ctx_mut()
                    .enum_type_keys
                    .insert(mangled_name.clone(), type_key);
                Some(mangled_name)
            }

            AType::Spec(spec_type) => {
                let name = spec_type.name.clone();
                self.cur_mod_ctx_mut()
                    .spec_type_keys
                    .insert(name.clone(), type_key);
                Some(name)
            }

            AType::Generic(generic_type) => {
                self.generic_type_keys
                    .insert(generic_type.clone(), type_key);
                None
            }

            AType::Function(fn_sig) => {
                self.fn_type_keys.insert(*fn_sig.clone(), type_key);
                None
            }

            AType::Tuple(tuple_type) => {
                self.tuple_type_keys.insert(tuple_type.clone(), type_key);
                None
            }

            AType::Array(array_type) => {
                self.array_type_keys.insert(array_type.clone(), type_key);
                None
            }

            AType::Pointer(ptr_type) => {
                self.pointer_type_keys.insert(ptr_type.clone(), type_key);
                None
            }

            _ => None,
        };

        // Make sure the type is resolvable in the current scope if it has a name.
        if let Some(mangled_name) = maybe_mangled_type_name {
            self.insert_type_key(Type::new_unresolved(mangled_name.as_str()), type_key);

            // Record the module in which the type was defined.
            self.type_declaration_mods
                .insert(type_key, self.cur_mod_path.clone());
        }

        type_key
    }

    /// Inserts the given analyzed type into the program context. This function will also handle
    /// tracking named types. If another matching type already exists in the current module,
    /// `typ` will not be inserted and the type key for the existing type will be returned.
    pub fn insert_type(&mut self, typ: AType) -> TypeKey {
        // Check if we've already inserted this type. This just prevents us
        // from storing duplicate types in the type store.
        if let Some(existing_tk) = self.get_existing_type_key(&typ) {
            return existing_tk;
        }

        self.force_insert_type(typ)
    }

    /// Records the mapping from `type_key` to the `spec_type_key` for the spec
    /// that is implemented by that type. Essentially, this records a record
    /// of the fact that a type implements a spec. Returns true if a record
    /// was newly inserted, and false otherwise (if one already existed).
    pub fn insert_spec_impl(&mut self, type_key: TypeKey, spec_type_key: TypeKey) -> bool {
        match self.spec_impls.get_mut(&type_key) {
            Some(spec_set) => spec_set.insert(spec_type_key),
            None => {
                self.spec_impls
                    .insert(type_key, HashSet::from([spec_type_key]));
                true
            }
        }
    }

    /// Tries to map the given un-analyzed type to a type key and return that type key. If there is
    /// no existing mapping for `typ`, performs semantic analysis on `typ`, inserts it into the
    /// type store and returns the resulting type key. An error will be recorded if
    /// the type is parameterized and invalid parameters were provided.
    pub fn resolve_type(&mut self, typ: &Type) -> TypeKey {
        self.resolve_type_helper(typ, false)
    }

    /// Does the same thing as `resolve_type`, except it doesn't require parameters
    /// for polymorphic types.  
    pub fn resolve_maybe_polymorphic_type(&mut self, typ: &Type) -> TypeKey {
        self.resolve_type_helper(typ, true)
    }

    /// Implements the functionality described in `resolve_type`, except that
    /// if `allow_polymorph` is `false` and the resolved type is polymorphic,
    /// an error will be recorded.
    fn resolve_type_helper(&mut self, typ: &Type, allow_polymorph: bool) -> TypeKey {
        if let Type::Unresolved(unresolved_type) = typ {
            if let Some(mod_name) = &unresolved_type.maybe_mod_name {
                // Make sure the module name is valid before looking up the type
                // in the corresponding module.
                if !self.check_mod_name(mod_name, typ) {
                    return self.unknown_type_key();
                };
            } else {
                if unresolved_type.name == "Self" {
                    return match self.get_cur_self_type_key() {
                        Some(tk) => tk,
                        None => {
                            self.insert_err(AnalyzeError::new(
                                ErrorKind::UndefType,
                                format_code!(
                                    "cannot use type {} outside of {} or {} block",
                                    "Self",
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

                // Check if the type refers to a generic parameter.
                if let Some(param) = self.get_param(unresolved_type.name.as_str()) {
                    return param.generic_type_key;
                }

                if let Some(key) = self.primitive_type_keys.get(unresolved_type.name.as_str()) {
                    return *key;
                }
            }

            if let Some(tk) = self.get_type_key_by_type_name(
                unresolved_type.maybe_mod_name.as_ref(),
                unresolved_type.name.as_str(),
            ) {
                return if unresolved_type.params.is_empty() {
                    // No parameters were provided, so this type should either be monomorphic, or
                    // `allow_polymorph` should be `true`.
                    let resolved_type = self.must_get_type(tk);
                    if resolved_type.params().is_some() && !allow_polymorph {
                        self.insert_err(AnalyzeError::new(
                            ErrorKind::UnresolvedParams,
                            "expected generic parameters",
                            typ,
                        ));
                    }

                    tk
                } else {
                    // Parameters were provided for the type, so we need to monomorphize it before
                    // returning it.
                    self.monomorphize_parameterized_type(
                        tk,
                        unresolved_type.params.as_ref(),
                        unresolved_type,
                    )
                };
            }
        }

        if let Some(key) = self
            .cur_mod_ctx()
            .search_stack(|scope| scope.get_type_key(&typ))
        {
            return key;
        };

        let a_type = AType::from(self, &typ);
        if a_type.is_unknown() {
            return self.unknown_type_key();
        }

        let is_generic = a_type.is_generic();
        let is_polymorphic = a_type.params().is_some();
        let key = self.insert_type(a_type);

        // Only record the type mapping for non-generic types.
        if !is_generic {
            self.insert_type_key(typ.clone(), key);
        }

        // It's possible that we just resolved a polymorphic type that was not defined before now.
        // If so, we should try to monomorphize it.
        if is_polymorphic {
            match typ {
                Type::Unresolved(unresolved_type) if !unresolved_type.params.is_empty() => {
                    return self.monomorphize_parameterized_type(key, &unresolved_type.params, typ);
                }
                _ => {}
            }

            if !allow_polymorph {
                self.insert_err(AnalyzeError::new(
                    ErrorKind::UnresolvedParams,
                    "expected generic parameters",
                    typ,
                ));
            }
        }

        key
    }

    /// Tries to locate and return the type key associated with the type with the given name.
    pub fn get_type_key_by_type_name(
        &self,
        maybe_mod_name: Option<&String>,
        name: &str,
    ) -> Option<TypeKey> {
        if maybe_mod_name.is_none() {
            if let Some(tk) = self.primitive_type_keys.get(name) {
                return Some(*tk);
            }

            // Look for a generic param with a matching name.
            if let Some(param) = self.get_param(name) {
                return Some(param.generic_type_key);
            }
        }

        let mod_ctx = self.get_mod_ctx(maybe_mod_name);

        // Try searching for the mangled type name first. If that doesn't work, we'll try with the
        // regular name. We have to do this to account for cases where a type is defined inside a
        // function.
        let mangled_name = self.mangle_name(maybe_mod_name, None, name, true);
        let typ = Type::new_unresolved(mangled_name.as_str());
        if let Some(tk) = mod_ctx.search_stack(|scope| scope.get_type_key(&typ)) {
            return Some(tk);
        }

        // Try searching for the mangled name without the current path.
        let mangled_name = self.mangle_name(maybe_mod_name, None, name, false);
        let typ = Type::new_unresolved(mangled_name.as_str());
        if let Some(tk) = mod_ctx.search_stack(|scope| scope.get_type_key(&typ)) {
            return Some(tk);
        }

        let typ = Type::new_unresolved(name);
        mod_ctx.search_stack(|scope| scope.get_type_key(&typ))
    }

    pub fn monomorphize_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) -> Option<TypeKey> {
        let typ = self.must_get_type(type_key);
        match typ {
            AType::Struct(_) => self.monomorphize_struct_type(type_key, type_mappings),
            AType::Enum(_) => self.monomorphize_enum_type(type_key, type_mappings),
            AType::Tuple(_) => self.monomorphize_tuple_type(type_key, type_mappings),
            AType::Array(_) => self.monomorphize_array_type(type_key, type_mappings),
            AType::Function(_) => self.monomorphize_fn_type(type_key, type_mappings),
            AType::Pointer(_) => self.monomorphize_ptr_type(type_key, type_mappings),
            AType::Spec(_) => {
                todo!()
            }

            // These types can't be monomorphized.
            AType::Bool
            | AType::U8
            | AType::I8
            | AType::U32
            | AType::I32
            | AType::F32
            | AType::I64
            | AType::U64
            | AType::F64
            | AType::Int
            | AType::Uint
            | AType::Str
            | AType::Generic(_)
            | AType::Unknown(_) => None,
        }
    }

    fn monomorphize_struct_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) -> Option<TypeKey> {
        let mut replaced_tks = false;
        let mut struct_type = self.must_get_type(type_key).to_struct_type().clone();
        for field in &mut struct_type.fields {
            if self.replace_tk(&mut field.type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        let has_replaced_param = match self.must_get_type(type_key).params() {
            Some(params) => params
                .params
                .iter()
                .find(|p| type_mappings.contains_key(&p.generic_type_key))
                .is_some(),
            None => false,
        };

        if replaced_tks || has_replaced_param {
            // Add monomorphized types to the name to disambiguate it from other
            // monomorphized instances of this type.
            if let Some(params) = &struct_type.maybe_params {
                struct_type.mangled_name += mangle_param_names(params, type_mappings).as_str();
            } else {
                for (target_tk, replacement_tk) in type_mappings {
                    struct_type.mangled_name = struct_type.mangled_name.replace(
                        format!("{target_tk}").as_str(),
                        format!("{replacement_tk}").as_str(),
                    );
                }
            }

            // Remove parameters from the signature now that they're no longer relevant.
            struct_type.maybe_params = None;

            // Define the new type in the program context.
            return Some(self.insert_type(AType::Struct(struct_type)));
        }

        None
    }

    fn monomorphize_enum_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) -> Option<TypeKey> {
        let mut replaced_tks = false;
        let mut enum_type = self.must_get_type(type_key).to_enum_type().clone();
        for variant in &mut enum_type.variants.values_mut() {
            if let Some(variant_tk) = &mut variant.maybe_type_key {
                if self.replace_tk(variant_tk, type_mappings) {
                    replaced_tks = true;
                }
            }
        }

        if replaced_tks {
            // Add monomorphized types to the name to disambiguate it from other
            // monomorphized instances of this type.
            if let Some(params) = &enum_type.maybe_params {
                enum_type.mangled_name += mangle_param_names(params, type_mappings).as_str();
            } else {
                for (target_tk, replacement_tk) in type_mappings {
                    enum_type.mangled_name = enum_type.mangled_name.replace(
                        format!("{target_tk}").as_str(),
                        format!("{replacement_tk}").as_str(),
                    );
                }
            }

            // Remove parameters from the signature now that they're no longer relevant.
            enum_type.maybe_params = None;

            // Define the new type in the program context.
            return Some(self.insert_type(AType::Enum(enum_type)));
        }

        None
    }

    fn monomorphize_fn_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) -> Option<TypeKey> {
        let mut replaced_tks = false;
        let mut fn_sig = self.must_get_type(type_key).to_fn_sig().clone();

        for arg in &mut fn_sig.args {
            if self.replace_tk(&mut arg.type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        if let Some(ret_type_key) = &mut fn_sig.maybe_ret_type_key {
            if self.replace_tk(ret_type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        if let Some(impl_type_key) = &mut fn_sig.maybe_impl_type_key {
            if self.replace_tk(impl_type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        if let Some(params) = &fn_sig.params {
            for param in &params.params {
                if type_mappings.contains_key(&param.generic_type_key) {
                    replaced_tks = true;
                    break;
                }
            }
        }

        if replaced_tks {
            // Add monomorphized types to the name to disambiguate it from other
            // monomorphized instances of this function.
            if let Some(params) = &fn_sig.params {
                fn_sig.mangled_name += mangle_param_names(params, type_mappings).as_str();
            } else {
                for (target_tk, replacement_tk) in type_mappings {
                    fn_sig.mangled_name = fn_sig.mangled_name.replace(
                        format!("{target_tk}").as_str(),
                        format!("{replacement_tk}").as_str(),
                    );
                }
            }

            // Remove parameters from the signature now that they're no longer relevant.
            fn_sig.params = None;

            // Define the new type in the program context.
            let new_fn_type_key = self.insert_type(AType::Function(Box::new(fn_sig.clone())));
            fn_sig.type_key = new_fn_type_key;
            self.replace_type(new_fn_type_key, AType::Function(Box::new(fn_sig.clone())));
            return Some(new_fn_type_key);
        }

        None
    }

    fn monomorphize_tuple_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) -> Option<TypeKey> {
        let mut tuple_type = self.must_get_type(type_key).to_tuple_type().clone();
        let mut replaced_tks = false;
        for field in &mut tuple_type.fields {
            if self.replace_tk(&mut field.type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        if replaced_tks {
            return Some(self.insert_type(AType::Tuple(tuple_type)));
        }

        None
    }

    fn monomorphize_array_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) -> Option<TypeKey> {
        let mut array_type = self.must_get_type(type_key).to_array_type().clone();
        if let Some(elem_tk) = &mut array_type.maybe_element_type_key {
            if self.replace_tk(elem_tk, type_mappings) {
                return Some(self.insert_type(AType::Array(array_type)));
            }
        }

        None
    }

    fn monomorphize_ptr_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) -> Option<TypeKey> {
        let mut ptr_type = self.must_get_type(type_key).to_ptr_type().clone();
        if self.replace_tk(&mut ptr_type.pointee_type_key, type_mappings) {
            return Some(self.insert_type(AType::Pointer(ptr_type)));
        }

        None
    }

    fn replace_tk(&mut self, tk: &mut TypeKey, type_mappings: &HashMap<TypeKey, TypeKey>) -> bool {
        // Check if we can just replace the type key itself based on the provided mapping.
        if let Some(replacement_tk) = type_mappings.get(tk) {
            *tk = *replacement_tk;
            return true;
        }

        let typ = self.must_get_type(*tk);

        let result = if let Some(params) = typ.params() {
            // The type is polymorphic, so we can use its defined parameters to extract monomorphization
            // info.
            let mut param_tks = vec![];
            for param in &params.params {
                param_tks.push(*type_mappings.get(&param.generic_type_key).unwrap());
            }

            Some((*tk, param_tks))
        } else if let Some(mono) = self.type_monomorphizations.get(tk) {
            let mono = mono.clone();

            // The type is a monomorphization of a polymorphic type. We can find the polymorphic type
            // and use it to extract monomorphization info.
            let mut param_tks = vec![];
            for replaced_param in &mono.replaced_params {
                let mut param_tk = replaced_param.replacement_type_key;
                self.replace_tk(&mut param_tk, type_mappings);
                param_tks.push(param_tk);
            }

            Some((mono.poly_type_key, param_tks))
        } else {
            // The type is just a regular type - not a polymorph or a monomorphization of anything.
            None
        };

        // If we were able to find a polymorphic type, we can now do the monomorphization.
        if let Some((poly_tk, param_tks)) = result {
            let dummy_span = Span::default();
            let dummy_spans = param_tks.iter().map(|_| &dummy_span).collect();
            let mono_tk = self.try_execute_monomorphization(poly_tk, param_tks, dummy_spans);
            if mono_tk != *tk {
                *tk = mono_tk;
                return true;
            }
            return false;
        }

        // Just try to monomorphize the type the basic way.
        match self.monomorphize_type(*tk, type_mappings) {
            Some(mono_tk) => {
                if mono_tk != *tk {
                    *tk = mono_tk;
                    true
                } else {
                    false
                }
            }
            None => false,
        }
    }

    /// Converts the given type from a polymorphic (parameterized) type into a
    /// monomorph by substituting type keys for generic types with those from
    /// the provided parameter types. Returns the type key for the monomorphized
    /// type.
    pub fn monomorphize_parameterized_type<T: Locatable>(
        &mut self,
        poly_type_key: TypeKey,
        param_types: &Vec<Type>,
        loc: &T,
    ) -> TypeKey {
        // Look up the type and make sure it's actually polymorphic.
        let poly_type = self.must_get_type(poly_type_key).clone();
        let defined_params = match poly_type.params() {
            Some(params) => &params.params,

            // The type is not polymorphic.
            None => {
                self.insert_err(
                    AnalyzeError::new(
                        ErrorKind::UnexpectedParams,
                        "unexpected generic parameters",
                        loc,
                    )
                    .with_detail(
                        format_code!(
                            "Type {} is not polymorphic.",
                            self.display_type(poly_type_key)
                        )
                        .as_str(),
                    ),
                );
                return poly_type_key;
            }
        };

        // Make sure the right number of params were provided.
        let expected_num_params = defined_params.len();
        let passed_num_params = param_types.len();
        if expected_num_params != passed_num_params {
            self.insert_err(AnalyzeError::new(
                ErrorKind::WrongNumberOfParams,
                format!(
                    "expected {} generic parameter{}, but found {}",
                    expected_num_params,
                    match expected_num_params > 1 {
                        true => "s",
                        false => "",
                    },
                    passed_num_params
                )
                .as_str(),
                loc,
            ));
            return poly_type_key;
        }

        let param_type_keys: Vec<TypeKey> =
            param_types.iter().map(|t| self.resolve_type(t)).collect();
        let param_locs: Vec<&Type> = param_types.iter().map(|t| t).collect();
        self.try_execute_monomorphization(poly_type_key, param_type_keys, param_locs)
    }

    fn try_execute_monomorphization<T: Locatable>(
        &mut self,
        poly_type_key: TypeKey,
        param_type_keys: Vec<TypeKey>,
        param_locs: Vec<&T>,
    ) -> TypeKey {
        let poly_type = self.must_get_type(poly_type_key);
        let defined_params = poly_type.params().unwrap().params.clone();

        // Generate a monomorphization for this type. We'll use this to track
        // the fact that this type has been monomorphized.
        let mut mono = Monomorphization {
            poly_type_key,
            mono_type_key: 0,
            replaced_params: vec![],
        };
        let mut type_mappings: HashMap<TypeKey, TypeKey> = HashMap::new();
        let mut all_type_keys_match = true;
        let mut param_checks_failed = false;
        let type_display = self.display_type(poly_type_key);

        for (param, (passed_param_tk, param_loc)) in defined_params
            .iter()
            .zip(param_type_keys.iter().zip(param_locs.iter()))
        {
            match self.check_param(*passed_param_tk, *param_loc, param, &type_display) {
                Ok(param_tk) => {
                    mono.replaced_params.push(ReplacedParam {
                        param_type_key: param.generic_type_key,
                        replacement_type_key: param_tk,
                    });

                    type_mappings.insert(param.generic_type_key, param_tk);

                    if param.generic_type_key != param_tk {
                        all_type_keys_match = false;
                    }
                }

                Err(e) => {
                    self.insert_err(e);
                    param_checks_failed = true;
                }
            }
        }

        if param_checks_failed {
            return self.unknown_type_key();
        }

        // Check if we're monomorphizing a type with its own generic parameters. If so, we can just
        // return the original polymorphic type's key.
        if all_type_keys_match {
            return poly_type_key;
        }

        // Check if the type has already been monomorphized. If so, return the
        // existing monomorphic type's key.
        if let Some(monos) = self.monomorphized_types.get(&poly_type_key) {
            if let Some(existing_mono) = monos.get(&mono) {
                return existing_mono.mono_type_key;
            }
        }

        // Monomorphize the type.
        mono.mono_type_key = match self.monomorphize_type(poly_type_key, &type_mappings) {
            Some(replacement_tk) => replacement_tk,
            // It turns out the type doesn't need monomorphization.
            None => return poly_type_key,
        };

        // Insert the monomorphization so we know we need to generate code
        // for it during codegen.
        self.insert_monomorphization(mono.clone());

        let mono_type_key = mono.mono_type_key;

        // Monomorphize all member functions on the polymorphic type.
        self.monomorphize_mem_fns(&mono, &type_mappings);

        // Mark this new monomorphic type as implementing the specs its polymorphic
        // counterpart implements.
        if let Some(spec_impl_tks) = self.spec_impls.get(&poly_type_key) {
            for spec_impl_tk in spec_impl_tks.clone() {
                self.insert_spec_impl(mono.mono_type_key, spec_impl_tk);
            }
        };

        mono_type_key
    }

    /// Monomorphizes all the member functions for the type monomorphized with
    /// the given monomorphization.
    fn monomorphize_mem_fns(
        &mut self,
        mono: &Monomorphization,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) {
        // Collect all member functions on the polymorphic type.
        let mut poly_mem_fn_tks = HashMap::new();
        if let Some(mem_fns) = self.type_member_fn_sigs.get(&mono.poly_type_key) {
            for (fn_name, fn_sig) in mem_fns {
                poly_mem_fn_tks.insert(fn_name.clone(), fn_sig.type_key);
            }
        }

        // Monomorphize all member functions.
        let mut mono_mem_fn_sigs = HashMap::new();
        for (fn_name, poly_mem_fn_tk) in poly_mem_fn_tks {
            if let Some(mono_tk) = self.monomorphize_fn_type(poly_mem_fn_tk, type_mappings) {
                let mono_fn_sig = self.must_get_type(mono_tk).to_fn_sig();
                mono_mem_fn_sigs.insert(fn_name, mono_fn_sig.clone());
            }
        }

        // Mark monomorphic member functions as public where necessary, and mark the monomorphic
        // type as an implementer of these functions.
        if !mono_mem_fn_sigs.is_empty() {
            for fn_name in mono_mem_fn_sigs.keys() {
                if self.member_fn_is_pub(mono.poly_type_key, fn_name.as_str()) {
                    self.mark_member_fn_pub(mono.mono_type_key, fn_name.as_str());
                }
            }

            self.type_member_fn_sigs
                .insert(mono.mono_type_key, mono_mem_fn_sigs);
        }
    }

    /// Analyzes a passed parameter type and checks that it matches the expected
    /// parameter constraints.
    fn check_param<T: Locatable>(
        &mut self,
        param_type_key: TypeKey,
        param_loc: &T,
        expected_param: &AParam,
        type_display: &String,
    ) -> AnalyzeResult<TypeKey> {
        let passed_param_type = self.must_get_type(param_type_key);

        // Skip further validation if the param value already failed analysis.
        if passed_param_type.is_unknown() {
            return Ok(param_type_key);
        }

        // Make sure the type passed as the parameter is not a spec.
        if passed_param_type.is_spec() {
            return Err(AnalyzeError::new(
                ErrorKind::MismatchedTypes,
                "expected concrete or generic type, but found spec",
                param_loc,
            )
            .with_detail(
                format_code!(
                    "Expected a concrete or generic type in place of parameter {} on \
                    {}, but found spec {}.",
                    expected_param.name,
                    type_display,
                    passed_param_type.to_spec_type().name,
                )
                .as_str(),
            ));
        }

        // Make sure that the type passed as the parameter value implements
        // the required specs.
        let missing_spec_type_keys =
            self.get_missing_spec_impls(param_type_key, expected_param.generic_type_key);
        let missing_spec_names: Vec<String> = missing_spec_type_keys
            .into_iter()
            .map(|tk| self.display_type(tk))
            .collect();
        if !missing_spec_names.is_empty() {
            let param_type_display = self.display_type(param_type_key);
            return Err(AnalyzeError::new(
                ErrorKind::SpecNotSatisfied,
                format_code!("type {} violates parameter constraints", param_type_display).as_str(),
                param_loc,
            )
            .with_detail(
                format!(
                    "Type {} does not implement the following specs required \
                    by parameter {} on {}: {}",
                    format_code!(param_type_display),
                    format_code!(expected_param.name),
                    format_code!(type_display),
                    format_code_vec(&missing_spec_names, ", ")
                )
                .as_str(),
            ));
        }

        Ok(param_type_key)
    }

    /// Inserts the given monomorphization into the program context.
    fn insert_monomorphization(&mut self, mono: Monomorphization) {
        self.type_monomorphizations
            .insert(mono.mono_type_key, mono.clone());

        match self.monomorphized_types.get_mut(&mono.poly_type_key) {
            Some(set) => {
                set.insert(mono);
            }
            None => {
                self.monomorphized_types
                    .insert(mono.poly_type_key, HashSet::from([mono]));
            }
        };
    }

    /// If `type_key` corresponds to a type that was produced by a monomorphization,
    /// this function returns the type key of its corresponding polymorphic type.
    pub fn get_poly_type_key(&self, mono_tk: TypeKey) -> Option<TypeKey> {
        match self.type_monomorphizations.get(&mono_tk) {
            Some(mono) => Some(mono.poly_type_key),
            None => None,
        }
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

    /// Returns the type key for the `i8` type.
    pub fn i8_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("i8").unwrap()
    }

    /// Returns the type key for the `u8` type.
    pub fn u8_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("u8").unwrap()
    }

    /// Returns the type key for the `i32` type.
    pub fn i32_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("i32").unwrap()
    }

    /// Returns the type key for the `u32` type.
    pub fn u32_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("u32").unwrap()
    }

    /// Returns the type key for the `f32` type.
    pub fn f32_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("f32").unwrap()
    }

    /// Returns the type key for the `i64` type.
    pub fn i64_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("i64").unwrap()
    }

    /// Returns the type key for the `u64` type.
    pub fn u64_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("u64").unwrap()
    }

    /// Returns the type key for the `f64` type.
    pub fn f64_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("f64").unwrap()
    }

    /// Returns the type key for the `int` type.
    pub fn int_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("int").unwrap()
    }

    /// Returns the type key for the `uint` type.
    pub fn uint_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("uint").unwrap()
    }

    /// Returns the type key for the `str` type.
    pub fn str_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("str").unwrap()
    }

    /// Returns the type key for the special `Self` type.
    pub fn self_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("Self").unwrap()
    }

    /// Pushes `scope` onto the stack.
    pub fn push_scope(&mut self, scope: Scope) {
        let mod_ctx = self.cur_mod_ctx_mut();
        match &scope.kind {
            ScopeKind::FnBody(_) => mod_ctx.fn_scope_indices.push(mod_ctx.stack.len()),
            ScopeKind::LoopBody => mod_ctx.loop_scope_indices.push(mod_ctx.stack.len()),
            ScopeKind::FromBody => mod_ctx.from_scope_indices.push(mod_ctx.stack.len()),
            _ => {}
        }

        mod_ctx.stack.push_back(scope);
    }

    /// Pops and returns the current scope from the stack.
    pub fn pop_scope(&mut self) -> Scope {
        let mod_ctx = self.cur_mod_ctx_mut();
        let scope = mod_ctx.stack.pop_back().unwrap();

        match &scope.kind {
            ScopeKind::FnBody(_) => {
                mod_ctx.fn_scope_indices.pop();
            }
            ScopeKind::LoopBody => {
                mod_ctx.loop_scope_indices.pop();
            }
            ScopeKind::FromBody => {
                mod_ctx.from_scope_indices.pop();
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

    /// Tries to insert the un-analyzed struct type into the current module context.
    /// Does nothing if the struct type has a type name that is already used.
    pub fn try_insert_unchecked_struct_type(&mut self, struct_type: StructType) {
        let name = struct_type.name.clone();
        if self.check_type_name_not_used(name.as_str(), &struct_type) {
            self.cur_mod_ctx_mut()
                .unchecked_struct_types
                .insert(name, struct_type);
        }
    }

    /// Tries to insert the un-analyzed enum type into the current module context.
    /// Does nothing if the enum type has a type name that is already used.
    pub fn try_insert_unchecked_enum_type(&mut self, enum_type: EnumType) {
        let name = enum_type.name.clone();
        if self.check_type_name_not_used(name.as_str(), &enum_type) {
            self.cur_mod_ctx_mut()
                .unchecked_enum_types
                .insert(name, enum_type);
        }
    }

    /// Tries to insert the un-analyzed spec into the current module context.
    /// Does nothing if the spec has a name that is already used.
    pub fn try_insert_unchecked_spec(&mut self, spec: Spec) {
        let name = spec.name.clone();
        if self.check_type_name_not_used(name.as_str(), &spec) {
            self.cur_mod_ctx_mut().unchecked_specs.insert(name, spec);
        }
    }

    /// Tries to insert the un-analyzed constant into the curren module context.
    /// Does nothing if the constant is already defined.
    pub fn try_insert_unchecked_const(&mut self, const_decl: Const) {
        let name = const_decl.name.clone();
        let symbol_already_defined = self.get_scoped_symbol(None, name.as_str()).is_some();
        let mod_ctx = self.cur_mod_ctx_mut();
        if symbol_already_defined || mod_ctx.unchecked_consts.get(name.as_str()).is_some() {
            self.insert_err(AnalyzeError::new(
                ErrorKind::DuplicateConst,
                format_code!("{} was already defined", const_decl.name).as_str(),
                &const_decl,
            ));
            return;
        }

        mod_ctx.unchecked_consts.insert(name, const_decl);
    }

    /// Removes the un-analyzed struct type with the given name from the current
    /// module context.
    pub fn remove_unchecked_struct_type(&mut self, name: &str) {
        self.cur_mod_ctx_mut().unchecked_struct_types.remove(name);
    }

    /// Removes the un-analyzed enum type with the given name from the current
    /// module context.
    pub fn remove_unchecked_enum_type(&mut self, name: &str) {
        self.cur_mod_ctx_mut().unchecked_enum_types.remove(name);
    }

    /// Marks the given type name as invalid in the current module context.
    pub fn insert_invalid_type_name(&mut self, name: String) {
        self.cur_mod_ctx_mut().invalid_type_names.insert(name);
    }

    /// Returns true if the given name is the name of a type that has been marked
    /// as invalid in the current module context.
    pub fn is_name_of_invalid_type(&self, name: &str) -> bool {
        self.cur_mod_ctx().invalid_type_names.contains(name)
    }

    /// Inserts the given function signature into the current module context, thereby
    /// declaring it as a defined function. This is done so we can locate function
    /// signatures before having analyzed their bodies.
    pub fn insert_defined_fn_sig(&mut self, sig: AFnSig) {
        let name = sig.name.clone();
        assert!(self
            .cur_mod_ctx_mut()
            .defined_fn_sigs
            .insert(name, sig)
            .is_none());
    }

    /// Gets the signature for the function with the given name in the module
    /// with the given name, or in the current module if `maybe_mod_name` is
    /// `None`.
    pub fn get_defined_fn_sig(
        &self,
        maybe_mod_name: Option<&String>,
        name: &str,
    ) -> Option<&AFnSig> {
        // Select the module to search in.
        let mod_ctx = self.get_mod_ctx(maybe_mod_name);
        mod_ctx.defined_fn_sigs.get(name)
    }

    /// Sets the type key associated with the current `impl` or `spec` type so it can be retrieved
    /// during analysis of the `impl` or `spec` body.
    pub fn set_cur_self_type_key(&mut self, maybe_type_key: Option<TypeKey>) {
        self.cur_mod_ctx_mut().cur_self_type_key = maybe_type_key;
    }

    /// Records the given name as a public constant name in the current module.
    pub fn insert_pub_const_name(&mut self, name: &str) {
        self.cur_mod_ctx_mut()
            .pub_const_names
            .insert(name.to_string());
    }

    /// Records the given name as a public type name in the current module.
    pub fn insert_pub_type_name(&mut self, name: &str) {
        self.cur_mod_ctx_mut()
            .pub_type_names
            .insert(name.to_string());
    }

    /// Records the given name as a public function name in the current module.
    pub fn insert_pub_fn_name(&mut self, name: &str) {
        self.cur_mod_ctx_mut().pub_fn_names.insert(name.to_string());
    }

    /// Records the given name as a public member function name on the given type
    /// in the current module.
    pub fn insert_pub_member_fn_name(&mut self, impl_type_key: TypeKey, name: &str) {
        self.cur_mod_ctx_mut()
            .pub_type_member_fn_names
            .insert(impl_type_key, name.to_string());
    }

    /// Sets the current module in the program context to `module`.
    /// If any of the imports have names that collide with existing imports in this module,
    /// they will not be mapped and error will be recorded for each conflict.
    pub fn set_cur_mod(&mut self, module: &Module) {
        self.cur_mod_path = module.path.clone();
        self.cur_mod_ctx_mut().imported_mod_paths = HashMap::with_capacity(module.used_mods.len());

        for used_mod in &module.used_mods {
            // If the import is declared with an alias, map it to the module path,
            // so we can resolve it later.
            let mod_name = if let Some(alias) = &used_mod.maybe_alias {
                if self
                    .cur_mod_ctx()
                    .imported_mod_paths
                    .get(alias.as_str())
                    .is_none()
                {
                    self.cur_mod_ctx_mut()
                        .imported_mod_paths
                        .insert(alias.to_string(), used_mod.path.raw.clone());
                } else {
                    self.insert_err(
                        AnalyzeError::new(
                            ErrorKind::DuplicateImportName,
                            format_code!("another import named {} already exists", alias).as_str(),
                            used_mod,
                        )
                        .with_detail(
                            format_code!(
                                "The name {} used for this import is not unique in this module.",
                                alias
                            )
                            .as_str(),
                        ),
                    );
                }

                alias.clone()
            } else {
                // There is no alias for this module, so just use the module
                // path as the module name.
                self.cur_mod_ctx_mut()
                    .imported_mod_paths
                    .insert(used_mod.path.raw.clone(), used_mod.path.raw.clone());
                used_mod.path.raw.clone()
            };

            // Resolve any imported identifiers from the module and add mappings
            // for each to the program context.
            for symbol in &used_mod.identifiers {
                // Set the symbol's module name so it gets resolved from the right
                // module.
                let mut symbol = symbol.clone();
                symbol.maybe_mod_name = Some(mod_name.clone());
                let a_symbol = ASymbol::from(self, &symbol, true, true, true, None);

                // Record an error and skip the symbol if its type could not be
                // resolved.
                if a_symbol.type_key == self.unknown_type_key() {
                    self.insert_err(AnalyzeError::new(
                        ErrorKind::UndefSymbol,
                        format_code!(
                            "{} is not defined in module {}",
                            symbol.name,
                            used_mod.path.raw
                        )
                        .as_str(),
                        &symbol,
                    ));
                    continue;
                }

                // Record an error if the symbol was not declared public.
                let mod_ctx = self.get_mod_ctx(Some(&mod_name));
                let is_pub = if a_symbol.is_const {
                    mod_ctx.pub_const_names.contains(symbol.name.as_str())
                } else if a_symbol.is_type {
                    mod_ctx.pub_type_names.contains(symbol.name.as_str())
                } else {
                    mod_ctx.pub_fn_names.contains(symbol.name.as_str())
                };

                if !is_pub {
                    self.insert_err(AnalyzeError::new(
                        ErrorKind::UseOfPrivateValue,
                        format_code!("{} is not public", a_symbol).as_str(),
                        &symbol,
                    ));
                }

                // Define the symbol in the program context.
                if a_symbol.is_type {
                    match self.type_store.must_get(a_symbol.type_key) {
                        AType::Struct(struct_type) => {
                            let mangled_name = struct_type.mangled_name.clone();
                            self.cur_mod_ctx_mut()
                                .struct_type_keys
                                .insert(mangled_name, a_symbol.type_key);
                        }

                        AType::Enum(enum_type) => {
                            let mangled_name = enum_type.mangled_name.clone();
                            self.cur_mod_ctx_mut()
                                .enum_type_keys
                                .insert(mangled_name, a_symbol.type_key);
                        }

                        AType::Pointer(ptr_type) => {
                            self.pointer_type_keys
                                .insert(ptr_type.clone(), a_symbol.type_key);
                        }

                        AType::Array(array_type) => {
                            self.array_type_keys
                                .insert(array_type.clone(), a_symbol.type_key);
                        }

                        AType::Tuple(tuple_type) => {
                            self.tuple_type_keys
                                .insert(tuple_type.clone(), a_symbol.type_key);
                        }

                        _ => {}
                    }

                    self.cur_mod_ctx_mut()
                        .stack
                        .front_mut()
                        .unwrap()
                        .insert_type_key(
                            Type::new_unresolved(symbol.name.as_str()),
                            a_symbol.type_key,
                        )
                } else {
                    let scoped_symbol =
                        ScopedSymbol::new_const(symbol.name.as_str(), a_symbol.type_key);
                    self.insert_symbol(scoped_symbol);
                }
            }
        }
    }

    /// Returns the type key associated with the current `impl` or `spec` type being analyzed.
    pub fn get_cur_self_type_key(&self) -> Option<TypeKey> {
        self.cur_mod_ctx().cur_self_type_key
    }

    /// Returns the member function with the given name on the type associated with `type_key`.
    pub fn get_member_fn(&self, type_key: TypeKey, fn_name: &str) -> Option<&AFnSig> {
        match self.type_member_fn_sigs.get(&type_key) {
            Some(member_fns) => member_fns.get(fn_name),
            None => None,
        }
    }

    /// Records the given member function as public in the program context.
    pub fn mark_member_fn_pub(&mut self, type_key: TypeKey, fn_name: &str) {
        match self.pub_member_fn_names.get_mut(&type_key) {
            Some(set) => {
                set.insert(fn_name.to_string());
            }
            None => {
                self.pub_member_fn_names
                    .insert(type_key, HashSet::from([fn_name.to_string()]));
            }
        }
    }

    /// Records the given struct field as public in the program context.
    pub fn mark_struct_field_pub(&mut self, type_key: TypeKey, field_name: &str) {
        match self.pub_struct_field_names.get_mut(&type_key) {
            Some(set) => {
                set.insert(field_name.to_string());
            }
            None => {
                self.pub_struct_field_names
                    .insert(type_key, HashSet::from([field_name.to_string()]));
            }
        }
    }

    /// Returns true if the field with the given name on the given struct type is
    /// accessible from the current module. This will be trie if the type is defined
    /// in this module or the field was declared public.
    pub fn struct_field_is_accessible(&self, type_key: TypeKey, field_name: &str) -> bool {
        // The struct field is considered accessible by default if the type is
        // just an inline type (i.e. not a named type declared separately).
        let is_anon = self
            .must_get_type(type_key)
            .to_struct_type()
            .name
            .is_empty();

        is_anon
            || self.type_declared_in_cur_mod(type_key)
            || self.struct_field_is_pub(type_key, field_name)
    }

    /// Returns true if the field with the given name on the given struct type is public.
    fn struct_field_is_pub(&self, type_key: TypeKey, field_name: &str) -> bool {
        match self.pub_struct_field_names.get(&type_key) {
            Some(map) => map.contains(field_name),
            None => false,
        }
    }

    /// Returns true if the member function is accessible from the current module.
    /// This will be true if the type is defined in this module or the function was
    /// declared public.
    pub fn member_fn_is_accessible(&self, type_key: TypeKey, fn_name: &str) -> bool {
        self.type_declared_in_cur_mod(type_key) || self.member_fn_is_pub(type_key, fn_name)
    }

    /// Returns true if the given type was declared in the current module.
    pub fn type_declared_in_cur_mod(&self, type_key: TypeKey) -> bool {
        match self.type_declaration_mods.get(&type_key) {
            Some(mod_path) => mod_path == &self.cur_mod_path,
            None => false,
        }
    }

    /// Returns true if the given type member function is public.
    fn member_fn_is_pub(&self, type_key: TypeKey, fn_name: &str) -> bool {
        // Generic types always have public member fns.
        if self.must_get_type(type_key).is_generic() {
            return true;
        }

        match self.pub_member_fn_names.get(&type_key) {
            Some(set) => set.contains(fn_name),
            None => false,
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
        self.cur_mod_ctx().unchecked_struct_types.get(name)
    }

    /// Returns the un-analyzed enum type with the given name.
    pub fn get_unchecked_enum_type(&self, name: &str) -> Option<&EnumType> {
        self.cur_mod_ctx().unchecked_enum_types.get(name)
    }

    /// Returns the un-analyzed spec with the given name.
    pub fn get_unchecked_spec(&self, name: &str) -> Option<&Spec> {
        self.cur_mod_ctx().unchecked_specs.get(name)
    }

    /// Tries to locate and return the un-analyzed constant with the given name.
    pub fn get_unchecked_const(&self, name: &str) -> Option<&Const> {
        self.cur_mod_ctx().unchecked_consts.get(name)
    }

    /// Returns all unchecked struct types in the current module context.
    pub fn unchecked_struct_types(&self) -> Vec<&StructType> {
        self.cur_mod_ctx().unchecked_struct_types.values().collect()
    }

    /// Returns all unchecked enum types in the program context.
    pub fn unchecked_enum_types(&self) -> Vec<&EnumType> {
        self.cur_mod_ctx().unchecked_enum_types.values().collect()
    }

    /// Returns true if the current scope is a function body or exists inside a function body.
    pub fn is_in_fn(&self) -> bool {
        !self.cur_mod_ctx().fn_scope_indices.is_empty()
    }

    /// Returns true if the current scope is a `from` body or exists inside a `from` body.
    pub fn is_in_from_block(&self) -> bool {
        !self.cur_mod_ctx().from_scope_indices.is_empty()
    }

    /// Returns a name mangled to the following form.
    ///
    ///     <mod_path>::<type_prefix><path><name>
    ///
    /// where
    ///  - `mod_path` is the full path of the module in which the symbol is
    ///    defined (determined by `maybe_mod_name`)
    ///  - `type_prefix` has the form `<type>.` if there is an impl type on
    ///    the function (determined by `maybe_impl_type_key`), or is empty
    ///  - `path` has the form `<f1>.<f2>...` where each item in the sequence
    ///    is the name of a function inside which the next function is nested
    ///    (this only applies if `include_fn_path` is `true`)
    ///  - `<name>` is the name of the symbol.
    ///
    /// If `include_path` is false, `path` will not be included.
    pub fn mangle_name(
        &self,
        maybe_mod_name: Option<&String>,
        maybe_impl_type_key: Option<TypeKey>,
        name: &str,
        include_path: bool,
    ) -> String {
        let mod_ctx = self.cur_mod_ctx();
        let mod_path = match maybe_mod_name {
            Some(name) => mod_ctx.imported_mod_paths.get(name).unwrap(),
            None => self.cur_mod_path.as_str(),
        };

        let type_prefix = match maybe_impl_type_key {
            Some(impl_tk) => {
                let impl_type = self.must_get_type(impl_tk);
                let params_suffix = match impl_type.params() {
                    Some(params) => format!(
                        "[{}]",
                        vec_to_string(
                            &params.params.iter().map(|p| p.generic_type_key).collect(),
                            ",",
                        )
                    ),
                    None => "".to_string(),
                };
                format!("{}{}.", impl_type.name(), params_suffix)
            }
            None => "".to_string(),
        };

        if mod_ctx.fn_scope_indices.is_empty() || !include_path {
            return format!("{mod_path}::{type_prefix}{name}");
        }

        // Get a path to the function based on the current scope.
        let mut fn_path = "".to_string();
        for i in &mod_ctx.fn_scope_indices {
            let fn_name = match &mod_ctx.stack.get(*i).unwrap().kind {
                ScopeKind::FnBody(name) => name.as_str(),
                _ => unreachable!(),
            };
            fn_path = fn_path + fn_name + "::";
        }

        format!("{mod_path}::{type_prefix}{fn_path}{name}")
    }

    /// Returns a new name for an anonymous function created inside the current scope. This
    /// also has the side effect of incrementing the anonymous function count for the current
    /// scope.
    pub fn new_anon_fn_name(&mut self) -> String {
        let mod_ctx = self.cur_mod_ctx_mut();
        let scope = mod_ctx
            .stack
            .get_mut(*mod_ctx.fn_scope_indices.last().unwrap())
            .unwrap();
        format!("anon_fn::{}", scope.get_and_inc_fn_count())
    }

    /// Returns true if the current scope is a loop body or falls within a loop body.
    pub fn is_in_loop(&self) -> bool {
        !self.cur_mod_ctx().loop_scope_indices.is_empty()
    }

    /// Adds the symbol type key to the current scope in the current module context.
    /// This will only make the symbol resolvable within the current module.
    /// If there was already a symbol with the same name, returns the old symbol.
    pub fn insert_symbol(&mut self, symbol: ScopedSymbol) -> Option<ScopedSymbol> {
        self.cur_mod_ctx_mut()
            .stack
            .back_mut()
            .unwrap()
            .add_symbol(symbol)
    }

    /// Attempts to locate the symbol with the given name in the current module
    /// and returns it, if found.
    /// Note that only the current function body and the top-level scope will be
    /// searched. In other words, if we're inside function A that is declared inside
    /// function B, then we won't be able to resolve symbols defined in function B.
    pub fn get_scoped_symbol(
        &self,
        maybe_mod_name: Option<&String>,
        name: &str,
    ) -> Option<&ScopedSymbol> {
        let mod_ctx = self.get_mod_ctx(maybe_mod_name);
        mod_ctx.search_stack_ref(|scope| scope.get_symbol(name), false)
    }

    /// Adds the given function to the program context, so it can be looked up by full name in the
    /// future.
    pub fn insert_fn(&mut self, func: AFn) {
        self.cur_mod_ctx_mut()
            .funcs
            .insert(func.signature.mangled_name.clone(), func);
    }

    /// Tries to locate and return the function with the given full name in the
    /// current module context.
    pub fn get_fn(&self, maybe_mod_name: Option<&String>, name: &str) -> Option<&AFn> {
        let mod_ctx = self.get_mod_ctx(maybe_mod_name);
        mod_ctx.funcs.get(name)
    }

    /// Pushes `params` onto the parameter stack.
    pub fn push_params(&mut self, params: AParams) {
        self.params.push(params);
    }

    /// Pops the params at the top of the parameter stack.
    pub fn pop_params(&mut self) -> Option<AParams> {
        self.params.pop()
    }

    /// Returns the current module's params.
    pub fn cur_params(&self) -> Option<&AParams> {
        self.params.last()
    }

    /// Returns the parameter with the given name, if one exists.
    pub fn get_param(&self, name: &str) -> Option<&AParam> {
        match self.cur_params() {
            Some(params) => params.get(name),
            None => None,
        }
    }

    /// Returns the struct type with the given name in the given module.
    pub fn get_struct_type(
        &self,
        maybe_mod_name: Option<&String>,
        name: &str,
    ) -> Option<&AStructType> {
        let mod_ctx = self.get_mod_ctx(maybe_mod_name);
        let mangled_name = self.mangle_name(maybe_mod_name, None, name, false);
        if let Some(tk) = mod_ctx.struct_type_keys.get(mangled_name.as_str()) {
            return Some(self.must_get_type(*tk).to_struct_type());
        }

        None
    }

    /// Returns the enum type with the given name in the given module.
    pub fn get_enum_type(&self, maybe_mod_name: Option<&String>, name: &str) -> Option<&AEnumType> {
        let mod_ctx = self.get_mod_ctx(maybe_mod_name);
        if let Some(tk) = mod_ctx.enum_type_keys.get(name) {
            return Some(self.must_get_type(*tk).to_enum_type());
        }

        None
    }

    /// Returns the spec type with the given name in the given module.
    pub fn get_spec_type(&self, maybe_mod_name: Option<&String>, name: &str) -> Option<&ASpecType> {
        let mod_ctx = self.get_mod_ctx(maybe_mod_name);
        if let Some(tk) = mod_ctx.spec_type_keys.get(name) {
            return Some(self.must_get_type(*tk).to_spec_type());
        }

        None
    }

    /// Returns the expected return type key for the current function body scope.
    pub fn get_cur_expected_ret_type_key(&self) -> Option<TypeKey> {
        let mod_ctx = self.cur_mod_ctx();
        let fn_scope_index = *mod_ctx.fn_scope_indices.last().unwrap();
        mod_ctx.stack.get(fn_scope_index).unwrap().ret_type_key()
    }

    /// Returns the expected yield type key for the current from body scope, or
    /// `None` if there isn't one.
    pub fn get_cur_expected_yield_type_key(&self) -> Option<TypeKey> {
        let mod_ctx = self.cur_mod_ctx();
        let from_scope_index = *mod_ctx.from_scope_indices.last().unwrap();
        mod_ctx
            .stack
            .get(from_scope_index)
            .unwrap()
            .yield_type_key()
    }

    /// Sets the expected yield type key for the current do body scope. Panics
    /// if we're not in a `from` scope or the existing `from` scope already has
    /// a yield type key set.
    pub fn set_cur_expected_yield_type_key(&mut self, type_key: TypeKey) {
        let mod_ctx = self.cur_mod_ctx_mut();
        let from_scope_index = *mod_ctx.from_scope_indices.last().unwrap();
        assert!(
            mod_ctx
                .stack
                .get_mut(from_scope_index)
                .unwrap()
                .set_yield_type_key(Some(type_key))
                .is_none(),
            "existing yield type key was overwritten"
        );
    }

    /// Returns a string containing the human-readable version of the type corresponding to the
    /// given type key.
    pub fn display_type(&self, type_key: TypeKey) -> String {
        let typ = self.must_get_type(type_key);
        match typ {
            AType::Bool
            | AType::Str
            | AType::I8
            | AType::U8
            | AType::U32
            | AType::I32
            | AType::F32
            | AType::I64
            | AType::U64
            | AType::F64
            | AType::Int
            | AType::Uint => {
                format!("{}", typ)
            }

            AType::Struct(struct_type) => {
                format!("{}{}", struct_type.name, self.display_param_types(type_key))
            }

            AType::Enum(enum_type) => {
                format!("{}{}", enum_type.name, self.display_param_types(type_key))
            }

            AType::Spec(s) => s.name.clone(),

            AType::Tuple(tuple_type) => {
                let mut s = format!("{{");

                for (i, field) in tuple_type.fields.iter().enumerate() {
                    s += format!("{}", self.display_type(field.type_key)).as_str();

                    if i + 1 < tuple_type.fields.len() {
                        s += format!(", ").as_str();
                    }
                }

                s + format!("}}").as_str()
            }

            AType::Array(array_type) => match &array_type.maybe_element_type_key {
                Some(key) => {
                    format!("[{}; {}]", self.display_type(*key), array_type.len)
                }

                None => "[]".to_string(),
            },

            AType::Function(fn_sig) => {
                let name = fn_sig.name.as_str();
                let mut s = format!("fn {}", name);

                if let Some(params) = &fn_sig.params {
                    s += params.display(self).as_str();
                }

                s += "(";

                for (i, arg) in fn_sig.args.iter().enumerate() {
                    if i == 0 {
                        s += format!("{}", arg.display(self)).as_str();
                    } else {
                        s += format!(", {}", arg.display(self)).as_str();
                    }
                }

                s += ")";

                if let Some(tk) = &fn_sig.maybe_ret_type_key {
                    s += format!(": {}", self.display_type(*tk)).as_str();
                }

                s
            }

            AType::Pointer(ptr_type) => format!(
                "*{}{}",
                match ptr_type.is_mut {
                    true => "mut ",
                    false => "",
                },
                self.display_type(ptr_type.pointee_type_key)
            )
            .to_string(),

            AType::Generic(t) => t.name.clone(),

            AType::Unknown(name) => format!("{}", name),
        }
    }

    fn display_param_types(&self, type_key: TypeKey) -> String {
        let mut params = "".to_string();
        if let Some(mono) = self.type_monomorphizations.get(&type_key) {
            params += "[";
            for (i, replaced_param) in mono.replaced_params.iter().enumerate() {
                let param_display = self.display_type(replaced_param.replacement_type_key);

                match i {
                    0 => {
                        params += param_display.as_str();
                    }
                    _ => {
                        params += format!(", {}", param_display).as_str();
                    }
                }
            }

            params += "]";
        }

        params
    }

    /// Maps `const_name` to `const_value` in the program context so the value can be looked up by
    /// name.
    pub fn insert_const_value(&mut self, const_name: &str, const_value: AExpr) {
        self.cur_mod_ctx_mut()
            .const_values
            .insert(const_name.to_string(), const_value);
    }

    /// Returns the expression representing the value assigned to the constant with the given name.
    pub fn get_const_value(&self, name: &str) -> Option<&AExpr> {
        self.cur_mod_ctx().const_values.get(name)
    }
}

/// Mangles generic parameter types.
pub fn mangle_param_names(params: &AParams, type_mappings: &HashMap<TypeKey, TypeKey>) -> String {
    let mut mangled_name = "[".to_string();
    for (i, param) in params.params.iter().enumerate() {
        if let Some(mono_tk) = type_mappings.get(&param.generic_type_key) {
            if i == 0 {
                mangled_name += format!("{}", mono_tk).as_str();
            } else {
                mangled_name += format!(",{}", mono_tk).as_str();
            }
        }
    }
    mangled_name + "]"
}
