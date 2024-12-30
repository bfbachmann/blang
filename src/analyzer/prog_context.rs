use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{Hash, Hasher};

use crate::analyzer::ast::array::AArrayType;
use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::func::AFnSig;
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
use crate::analyzer::mangling;
use crate::analyzer::scope::{Scope, ScopeKind, ScopedSymbol};
use crate::analyzer::type_store::{GetType, TypeKey, TypeStore};
use crate::analyzer::warn::AnalyzeWarning;
use crate::fmt::format_code_vec;
use crate::lexer::pos::{Locatable, Position, Span};
use crate::parser::ast::r#const::Const;
use crate::parser::ast::r#enum::EnumType;
use crate::parser::ast::r#struct::StructType;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::spec::SpecType;
use crate::parser::ast::symbol::Symbol;
use crate::parser::ast::unresolved::UnresolvedType;
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

impl Monomorphization {
    pub fn type_mappings(&self) -> HashMap<TypeKey, TypeKey> {
        self.replaced_params
            .iter()
            .map(|rp| (rp.param_type_key, rp.replacement_type_key))
            .collect()
    }
}

/// Contains information about `impl` blocks for a type.
struct TypeImpls {
    /// Maps function name to function type key for all functions declared in default impl blocks
    /// (impl blocks without specs) for the type.
    default_fns: HashMap<String, TypeKey>,
    /// Maps implemented spec type key to a mapping from member function name to its type key.
    /// There should be one mapping for each spec impl on this type.
    spec_impls: HashMap<TypeKey, HashMap<String, TypeKey>>,
    /// Contains the type keys of all public member functions for this type.
    pub_fn_tks: HashSet<TypeKey>,
}

impl TypeImpls {
    fn new() -> TypeImpls {
        TypeImpls {
            default_fns: Default::default(),
            spec_impls: Default::default(),
            pub_fn_tks: Default::default(),
        }
    }

    /// Inserts information about an `impl` block for this type.
    fn insert_impl(&mut self, maybe_spec_tk: Option<TypeKey>, fns: HashMap<String, TypeKey>) {
        match maybe_spec_tk {
            Some(tk) => {
                assert!(self.spec_impls.insert(tk, fns).is_none());
            }
            None => {
                self.default_fns.extend(fns);
            }
        }
    }

    /// Inserts the given function info.
    fn insert_fn(&mut self, maybe_spec_tk: Option<TypeKey>, fn_name: String, fn_type_key: TypeKey) {
        match maybe_spec_tk {
            Some(spec_tk) => {
                self.spec_impls
                    .get_mut(&spec_tk)
                    .expect(format!("spec {spec_tk} should exist").as_str())
                    .insert(fn_name, fn_type_key);
            }
            None => {
                self.default_fns.insert(fn_name, fn_type_key);
            }
        }
    }

    /// Returns the type key for the spec that the given function implements.
    fn get_spec_type_key(&self, fn_type_key: TypeKey) -> Option<TypeKey> {
        for (spec_tk, fns) in &self.spec_impls {
            for fn_tk in fns.values() {
                if *fn_tk == fn_type_key {
                    return Some(*spec_tk);
                }
            }
        }

        None
    }

    /// Marks the given function as public.
    fn mark_fn_pub(&mut self, fn_type_key: TypeKey) {
        self.pub_fn_tks.insert(fn_type_key);
    }

    /// Tries to find a "default" function (i.e. a function declared in a regular `impl` block
    /// without a spec) with the given name.
    fn get_default_fn(&self, name: &str) -> Option<TypeKey> {
        self.default_fns.get(name).cloned()
    }

    /// Tries to find the function with the given name that is part of the implementation of the
    /// given spec.
    fn get_fn_from_spec_impl(&self, spec_tk: TypeKey, name: &str) -> Option<TypeKey> {
        match self.spec_impls.get(&spec_tk) {
            Some(impls) => impls.get(name).cloned(),
            None => None,
        }
    }

    /// Returns the type keys of all functions with the given name in all impls.
    fn get_fns_by_name(&self, name: &str) -> HashSet<TypeKey> {
        let mut fn_tks = HashSet::new();

        // Find a default function with the same name.
        if let Some(tk) = self.default_fns.get(name) {
            fn_tks.insert(*tk);
        }

        // Find any spec functions with the same name.
        for fns in self.spec_impls.values() {
            if let Some(tk) = fns.get(name) {
                fn_tks.insert(*tk);
            }
        }

        fn_tks
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
    /// Will contain the type key of the spec being implemented in the current `impl` or `spec`
    /// block, if any.
    cur_spec_type_key: Option<TypeKey>,
    /// Maps module name to full module path for each module that was imported into this
    /// module. For example, if an import was specified with `use "my_project/my_mod.bl"`, then
    /// this map would contain the mapping `"my_mod": "my_project/my_mod.bl"`.
    imported_mod_paths: HashMap<String, String>,

    /// The names of public constants defined in this module.
    pub_const_names: HashSet<String>,
    /// The names of public functions defined in this module.
    pub_fn_names: HashSet<String>,

    /// Contains the names of all types that have been marked as "invalid" by the analyzer. At the
    /// time of writing this, this should only be used for illegal cyclical types with infinite
    /// size.
    invalid_type_names: HashSet<String>,
    /// Maps un-analyzed struct names to un-analyzed structs.
    unchecked_struct_types: HashMap<String, StructType>,
    /// Maps un-analyzed enum names to un-analyzed enums.
    unchecked_enum_types: HashMap<String, EnumType>,
    /// Maps un-analyzed specs names to un-analyzed specs.
    unchecked_specs: HashMap<String, SpecType>,
    /// Maps constant names to un-analyzed constant values.
    unchecked_consts: HashMap<String, Const>,
    // Contains impl types and their specs for all unchecked impls blocks.
    unchecked_impls: Vec<(UnresolvedType, Option<Symbol>)>,
    /// Maps mangled function names to the type keys of analyzed function signatures.
    fn_types: HashMap<String, TypeKey>,
    /// Maps function names to analyzed function signatures only for regular functions (i.e. not
    /// function expressions, types, or member functions).
    funcs: HashMap<String, AFnSig>,
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
            cur_spec_type_key: None,
            imported_mod_paths: Default::default(),
            pub_const_names: Default::default(),
            pub_fn_names: Default::default(),
            invalid_type_names: Default::default(),
            unchecked_struct_types: Default::default(),
            unchecked_enum_types: Default::default(),
            unchecked_specs: Default::default(),
            unchecked_consts: Default::default(),
            unchecked_impls: vec![],
            fn_types: Default::default(),
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
    /// Contains the type keys of all types declared public.
    pub_type_keys: HashSet<TypeKey>,

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
    /// Maps type key to its impl blocks.
    type_impls: HashMap<TypeKey, TypeImpls>,
    /// Maps struct type key to the set of public field names on that struct type.
    pub_struct_field_names: HashMap<TypeKey, HashSet<String>>,
    /// Maps type keys to the paths of the modules in which the types are declared.
    type_declaration_mods: HashMap<TypeKey, String>,
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
    pub fn new(root_mod_path: &str, mod_paths: Vec<&str>) -> Self {
        let mut type_store = TypeStore::new();

        // Set up primitive type keys.
        let mut primitive_type_keys = HashMap::new();
        let mut type_declaration_mods = HashMap::new();
        for typ in AType::primitives() {
            let name = typ.name().to_string();
            let type_key = type_store.insert_type(typ);
            primitive_type_keys.insert(name.clone(), type_key);
            type_declaration_mods.insert(type_key, format!("std/builtins/{}.bl", name));
        }

        // Initialize empty module contexts.
        let mut mod_ctxs = HashMap::with_capacity(mod_paths.len());
        for mod_path in &mod_paths {
            mod_ctxs.insert(mod_path.to_string(), ModuleContext::new());
        }

        ProgramContext {
            type_store,
            primitive_type_keys,
            pub_type_keys: Default::default(),
            cur_mod_path: root_mod_path.to_string(),
            module_contexts: mod_ctxs,
            tuple_type_keys: Default::default(),
            array_type_keys: Default::default(),
            pointer_type_keys: Default::default(),
            generic_type_keys: Default::default(),
            fn_type_keys: Default::default(),
            type_impls: Default::default(),
            pub_struct_field_names: Default::default(),
            type_declaration_mods,
            params: vec![],
            monomorphized_types: Default::default(),
            type_monomorphizations: Default::default(),
            warnings: Default::default(),
            errors: Default::default(),
        }
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

    /// Returns the path of the module with the given name in the current context.
    pub fn get_mod_path(&self, mod_name: &str) -> Option<&String> {
        self.cur_mod_ctx().imported_mod_paths.get(mod_name)
    }

    /// Returns the path of the current module in the current context.
    pub fn get_cur_mod_path(&self) -> &String {
        &self.cur_mod_path
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

    /// Checks that the given type implements the set of specs on the given
    /// generic type. Returns type keys for specs not implemented by the type.
    pub fn get_missing_spec_impls(
        &mut self,
        type_key: TypeKey,
        generic_type_key: TypeKey,
    ) -> Vec<TypeKey> {
        let mut missing_spec_type_keys = vec![];
        let spec_type_keys = &self
            .get_type(generic_type_key)
            .to_generic_type()
            .spec_type_keys;

        for spec_type_key in spec_type_keys.clone() {
            if !self.type_has_spec_impl(type_key, spec_type_key)
                && !self.type_has_unchecked_spec_impl(type_key, spec_type_key)
            {
                missing_spec_type_keys.push(spec_type_key);
            }
        }

        missing_spec_type_keys
    }

    /// Returns true if the type with the given key implements the spec with the given key.
    pub fn type_has_spec_impl(&mut self, type_key: TypeKey, spec_type_key: TypeKey) -> bool {
        self.type_impls
            .get(&type_key)
            .is_some_and(|i| i.spec_impls.contains_key(&spec_type_key))
    }

    /// Returns true if type given type has an impl for the given spec that has not yet been
    /// analyzed.
    fn type_has_unchecked_spec_impl(&mut self, type_key: TypeKey, spec_type_key: TypeKey) -> bool {
        // We haven't yet analyzed an impl block on the type for the given spec, so let's see
        // if it appears in the unchecked impls.
        if self.type_declared_in_cur_mod(type_key) || self.type_declared_in_cur_mod(spec_type_key) {
            // TODO: this is expensive, we should only have to do it once. I'm not going to bother
            // fixing it for now, though, because it should be rare that this is needed anyway.
            for (impl_type, maybe_spec_type) in self.cur_mod_ctx().unchecked_impls.clone() {
                if let Some(spec) = maybe_spec_type {
                    let impl_tk = self.resolve_maybe_polymorphic_type(&Type::Unresolved(impl_type));
                    if impl_tk != type_key {
                        continue;
                    }

                    let impl_spec_tk = self.resolve_type(&spec.as_unresolved_type());
                    if impl_spec_tk == spec_type_key {
                        return true;
                    }
                }
            }
        }

        false
    }

    /// Returns a mapping from error start position to the error that occurred there.
    #[cfg(test)]
    pub fn errors(&self) -> &HashMap<Position, AnalyzeError> {
        &self.errors
    }

    /// Returns a mapping from warning start position to the warning that occurred there.
    #[cfg(test)]
    pub fn warnings(&self) -> &HashMap<Position, AnalyzeWarning> {
        &self.warnings
    }

    /// Drains all module constants from the program context.
    pub fn drain_mod_consts(&mut self) -> HashMap<String, HashMap<String, AExpr>> {
        let mut mod_consts = HashMap::new();

        for (mod_name, mod_ctx) in &mut self.module_contexts {
            mod_consts.insert(
                mod_name.to_owned(),
                std::mem::replace(&mut mod_ctx.const_values, HashMap::new()),
            );
        }

        mod_consts
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
        let type_key = self.type_store.insert_type(typ);

        // Create an additional mapping to the new type key to avoid type duplication, if necessary.
        let typ = self.get_type(type_key);
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
            self.replace_type(existing_tk, typ);
            return existing_tk;
        }

        self.force_insert_type(typ)
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
                let (resolved_tk, poly_tk) = if unresolved_type.params.is_empty() {
                    // No parameters were provided, so this type should either be monomorphic, or
                    // `allow_polymorph` should be `true`.
                    let resolved_type = self.get_type(tk);
                    if resolved_type.params().is_some() && !allow_polymorph {
                        self.insert_err(AnalyzeError::new(
                            ErrorKind::UnresolvedParams,
                            "expected generic parameters",
                            typ,
                        ));

                        return self.unknown_type_key();
                    }

                    (tk, tk)
                } else {
                    // Parameters were provided for the type, so we need to monomorphize it before
                    // returning it.
                    let mono_tk = self.monomorphize_parameterized_type(
                        tk,
                        unresolved_type.params.as_ref(),
                        unresolved_type,
                    );

                    (mono_tk, tk)
                };

                // If the type is foreign, make sure it's public.
                if unresolved_type.maybe_mod_name.is_some() && !self.type_is_pub(poly_tk) {
                    self.insert_err(AnalyzeError::new(
                        ErrorKind::UseOfPrivateValue,
                        format_code!("type {} is not public", self.display_type(poly_tk)).as_str(),
                        typ,
                    ));
                }

                return resolved_tk;
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

                return self.unknown_type_key();
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
        let mangled_name = self.mangle_name(maybe_mod_name, None, None, name, true);
        let typ = Type::new_unresolved(mangled_name.as_str());
        if let Some(tk) = mod_ctx.search_stack(|scope| scope.get_type_key(&typ)) {
            return Some(tk);
        }

        // Try searching for the mangled name without the current path.
        let mangled_name = self.mangle_name(maybe_mod_name, None, None, name, false);
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
        let typ = self.get_type(type_key);
        match typ {
            AType::Struct(_) => self.monomorphize_struct_type(type_key, type_mappings),
            AType::Enum(_) => self.monomorphize_enum_type(type_key, type_mappings),
            AType::Tuple(_) => self.monomorphize_tuple_type(type_key, type_mappings),
            AType::Array(_) => self.monomorphize_array_type(type_key, type_mappings),
            AType::Function(_) => self.monomorphize_fn_type(type_key, type_mappings),
            AType::Pointer(_) => self.monomorphize_ptr_type(type_key, type_mappings),
            AType::Spec(_) => self.monomorphize_spec_type(type_key, type_mappings),

            // These types can't be monomorphized.
            AType::Bool
            | AType::U8
            | AType::I8
            | AType::U16
            | AType::I16
            | AType::U32
            | AType::I32
            | AType::F32
            | AType::I64
            | AType::U64
            | AType::F64
            | AType::Int
            | AType::Uint
            | AType::Str
            | AType::Char
            | AType::Generic(_)
            | AType::Unknown(_) => None,
        }
    }

    fn monomorphize_struct_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) -> Option<TypeKey> {
        let mut struct_type = self.get_type(type_key).to_struct_type().clone();

        // We can't monomorphize struct types that aren't parameterized.
        if struct_type.maybe_params.is_none() {
            return None;
        }

        let mut replaced_tks = false;
        for field in &mut struct_type.fields {
            if self.replace_tks(&mut field.type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        let has_replaced_param = match self.get_type(type_key).params() {
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
                struct_type.mangled_name +=
                    mangling::mangle_param_names(params, type_mappings).as_str();
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
        let mut enum_type = self.get_type(type_key).to_enum_type().clone();
        for variant in &mut enum_type.variants.values_mut() {
            if let Some(variant_tk) = &mut variant.maybe_type_key {
                if self.replace_tks(variant_tk, type_mappings) {
                    replaced_tks = true;
                }
            }
        }

        if replaced_tks {
            // Add monomorphized types to the name to disambiguate it from other
            // monomorphized instances of this type.
            if let Some(params) = &enum_type.maybe_params {
                enum_type.mangled_name +=
                    mangling::mangle_param_names(params, type_mappings).as_str();
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
        let mut fn_sig = self.get_type(type_key).to_fn_sig().clone();

        for arg in &mut fn_sig.args {
            if self.replace_tks(&mut arg.type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        if let Some(ret_type_key) = &mut fn_sig.maybe_ret_type_key {
            if self.replace_tks(ret_type_key, type_mappings) {
                replaced_tks = true;
            }
        }

        if let Some(impl_type_key) = &mut fn_sig.maybe_impl_type_key {
            if self.replace_tks(impl_type_key, type_mappings) {
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
                fn_sig.mangled_name += mangling::mangle_param_names(params, type_mappings).as_str();
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
        let mut tuple_type = self.get_type(type_key).to_tuple_type().clone();
        let mut replaced_tks = false;
        for field in &mut tuple_type.fields {
            if self.replace_tks(&mut field.type_key, type_mappings) {
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
        let mut array_type = self.get_type(type_key).to_array_type().clone();
        if let Some(elem_tk) = &mut array_type.maybe_element_type_key {
            if self.replace_tks(elem_tk, type_mappings) {
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
        let mut ptr_type = self.get_type(type_key).to_ptr_type().clone();
        if self.replace_tks(&mut ptr_type.pointee_type_key, type_mappings) {
            return Some(self.insert_type(AType::Pointer(ptr_type)));
        }

        None
    }

    fn monomorphize_spec_type(
        &mut self,
        type_key: TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) -> Option<TypeKey> {
        let mut spec_type = self.get_type(type_key).to_spec_type().clone();
        let mut replaced_tks = false;

        for fn_tk in spec_type.member_fn_type_keys.values_mut() {
            if let Some(new_tk) = self.monomorphize_fn_type(*fn_tk, type_mappings) {
                *fn_tk = new_tk;
                replaced_tks = true;
            }
        }

        match replaced_tks {
            true => Some(self.insert_type(AType::Spec(spec_type))),
            false => None,
        }
    }

    /// Replaces type keys inside the given type using `type_mappings`. If any type keys were
    /// replaced, updates `tk`.
    pub fn replace_tks(
        &mut self,
        tk: &mut TypeKey,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) -> bool {
        // Check if we can just replace the type key itself based on the provided mapping.
        if let Some(replacement_tk) = type_mappings.get(tk) {
            *tk = *replacement_tk;
            return true;
        }

        let typ = self.get_type(*tk);

        let result = if let Some(params) = typ.params() {
            // The type is polymorphic, so we can use its defined parameters to extract
            // monomorphization info.
            let mut param_tks = vec![];
            for param in &params.params {
                param_tks.push(*type_mappings.get(&param.generic_type_key).unwrap());
            }

            Some((*tk, param_tks))
        } else if let Some(mono) = self.type_monomorphizations.get(tk) {
            let mono = mono.clone();

            // The type is a monomorphization of a polymorphic type. We can find the polymorphic
            // type and use it to extract monomorphization info.
            let mut param_tks = vec![];
            for replaced_param in &mono.replaced_params {
                let mut param_tk = replaced_param.replacement_type_key;
                self.replace_tks(&mut param_tk, type_mappings);
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
            let dummy_spans: Vec<&Span> = param_tks.iter().map(|_| &dummy_span).collect();
            let mono_tk =
                self.try_execute_monomorphization(poly_tk, param_tks, &dummy_spans, &dummy_span);
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
    pub fn monomorphize_parameterized_type(
        &mut self,
        poly_type_key: TypeKey,
        param_types: &Vec<Type>,
        loc: &impl Locatable,
    ) -> TypeKey {
        let param_type_keys: Vec<TypeKey> =
            param_types.iter().map(|t| self.resolve_type(t)).collect();
        let param_locs: Vec<&Type> = param_types.iter().map(|t| t).collect();
        self.try_execute_monomorphization(poly_type_key, param_type_keys, &param_locs, loc)
    }

    /// Re-executes a monomorphization.
    pub fn reexecute_monomorphization(&mut self, mono: Monomorphization) {
        // Temporarily remove the cached monomorphization to force a new one.
        let removed = self
            .type_monomorphizations
            .remove(&mono.mono_type_key)
            .unwrap();

        // Execute the same monomorphization again.
        self.monomorphize_type(mono.poly_type_key, &mono.type_mappings())
            .unwrap();

        // Re-insert the monomorphization.
        self.insert_monomorphization(removed);
    }

    // Tries to monomorphize the given polymorphic type using the given parameter types.
    pub fn try_execute_monomorphization(
        &mut self,
        poly_type_key: TypeKey,
        param_type_keys: Vec<TypeKey>,
        param_locs: &Vec<&impl Locatable>,
        loc: &impl Locatable,
    ) -> TypeKey {
        // Look up the type and make sure it's actually polymorphic.
        let poly_type = self.get_type(poly_type_key);
        let defined_params = match poly_type.params() {
            Some(params) => params.params.clone(),

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
        let passed_num_params = param_type_keys.len();
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

        // Generate a monomorphization for this type. We'll use this to track
        // the fact that this type has been monomorphized.
        let mut mono = Monomorphization {
            poly_type_key,
            // Since we haven't actually computed the monomorphization yet, we'll set its resulting
            // mono type key to the poly type key for now. This way we'll avoid infinite recursive
            // monomorphization of the type in cases where is references itself. Later (below),
            // after the type has been monomorphized, we'll replace all instances of this poly type
            // key with the correct mono type key.
            mono_type_key: poly_type_key,
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

        // Before we proceed with monomorphization, we'll preemptively track the monomorphization
        // to prevent infinitely recursive monomorphization. This is important for types that
        // contain references to types that are monomorphizations of themselves.
        self.insert_monomorphization(mono.clone());

        // Monomorphize the type.
        mono.mono_type_key = match self.monomorphize_type(poly_type_key, &type_mappings) {
            Some(replacement_tk) => replacement_tk,
            // It turns out the type doesn't need monomorphization.
            None => return poly_type_key,
        };

        // TODO: Replace all instances of the polymorphic type key with the new monomorphic type key
        // now that we've completed the monomorphization.

        // Insert the monomorphization so we know we need to generate code
        // for it during codegen.
        self.insert_monomorphization(mono.clone());

        // Mark this new monomorphic type as implementing the specs its polymorphic
        // counterpart implements.
        if let Some(impls) = self.type_impls.get(&poly_type_key) {
            let spec_type_keys: Vec<TypeKey> = impls.spec_impls.keys().cloned().collect();
            for spec_tk in spec_type_keys {
                self.insert_impl(mono.mono_type_key, Some(spec_tk), HashMap::new());
            }
        }

        mono.mono_type_key
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
        let passed_param_type = self.get_type(param_type_key);

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
                    "{} does not implement spec{} {} required \
                    by parameter {} in {}.",
                    format_code!(param_type_display),
                    match missing_spec_names.len() {
                        1 => "",
                        _ => "s",
                    },
                    format_code_vec(&missing_spec_names, ", "),
                    format_code!(expected_param.name),
                    format_code!(type_display),
                )
                .as_str(),
            ));
        }

        Ok(param_type_key)
    }

    /// Inserts the given monomorphization into the program context.
    fn insert_monomorphization(&mut self, mono: Monomorphization) {
        if mono.mono_type_key != self.unknown_type_key() {
            self.type_monomorphizations
                .insert(mono.mono_type_key, mono.clone());
        }

        match self.monomorphized_types.get_mut(&mono.poly_type_key) {
            Some(set) => {
                set.replace(mono);
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

    /// Returns the type key for the `i16` type.
    pub fn i16_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("i16").unwrap()
    }

    /// Returns the type key for the `u16` type.
    pub fn u16_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("u16").unwrap()
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

    /// Returns the type key for the `char` type.
    pub fn char_type_key(&self) -> TypeKey {
        *self.primitive_type_keys.get("char").unwrap()
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
    pub fn get_type(&self, type_key: TypeKey) -> &AType {
        self.type_store.get_type(type_key)
    }

    /// Replaces the existing type associated with `type_key` with `typ`.
    pub fn replace_type(&mut self, type_key: TypeKey, typ: AType) {
        self.type_store.replace_type(type_key, typ);
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
    pub fn try_insert_unchecked_spec(&mut self, spec: SpecType) {
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

    /// Inserts an un-analyzed impl header (the impl type and optional spec being implemented)
    /// into the current module context so we can look it up later to see if that type implements
    /// that spec. That lookup should only be necessary if we're trying to figure out if a type
    /// implements a spec before we've analyzed the impl where the spec is implemented for the type.
    pub fn insert_unchecked_impl(&mut self, impl_type: UnresolvedType, maybe_spec: Option<Symbol>) {
        self.cur_mod_ctx_mut()
            .unchecked_impls
            .push((impl_type, maybe_spec));
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

    /// Stores a mapping from the given mangled function name to its type key.
    pub fn insert_fn_sig(&mut self, mangled_name: &str, type_key: TypeKey) {
        assert!(self
            .cur_mod_ctx_mut()
            .fn_types
            .insert(mangled_name.to_string(), type_key)
            .is_none());
    }

    /// Gets the signature for the function with the given mangled name in the module
    /// with the given name, or in the current module if `maybe_mod_name` is `None`.
    pub fn get_fn_sig_by_mangled_name(
        &self,
        maybe_mod_name: Option<&String>,
        mangled_name: &str,
    ) -> Option<&AFnSig> {
        let mod_ctx = self.get_mod_ctx(maybe_mod_name);
        match mod_ctx.fn_types.get(mangled_name) {
            Some(tk) => Some(self.get_type(*tk).to_fn_sig()),
            None => None,
        }
    }

    /// Sets the type key associated with the current `impl` or `spec` type so it can be retrieved
    /// during analysis of the `impl` or `spec` body.
    pub fn set_cur_self_type_key(&mut self, maybe_type_key: Option<TypeKey>) {
        self.cur_mod_ctx_mut().cur_self_type_key = maybe_type_key;
    }

    /// Sets the type key of the spec implemented by the current `impl` block to
    /// `maybe_spec_type_key`.
    pub fn set_cur_spec_type_key(&mut self, maybe_spec_type_key: Option<TypeKey>) {
        // Assert that the type is actually a spec.
        assert!(match maybe_spec_type_key {
            Some(spec_tk) => self.get_type(spec_tk).is_spec(),
            None => true,
        });

        self.cur_mod_ctx_mut().cur_spec_type_key = maybe_spec_type_key;
    }

    /// Records the given name as a public constant name in the current module.
    pub fn insert_pub_const_name(&mut self, name: &str) {
        self.cur_mod_ctx_mut()
            .pub_const_names
            .insert(name.to_string());
    }

    /// Records the given name as a public type name in the current module.
    pub fn mark_type_pub(&mut self, type_key: TypeKey) {
        self.pub_type_keys.insert(type_key);
    }

    /// Returns true if the type with the given name in the given module is public.
    pub fn type_is_pub(&self, type_key: TypeKey) -> bool {
        let type_key = match self.type_monomorphizations.get(&type_key) {
            Some(mono) => mono.poly_type_key,
            None => type_key,
        };

        self.pub_type_keys.contains(&type_key) || self.get_type(type_key).is_primitive()
    }

    /// Records the given name as a public function name in the current module.
    pub fn insert_pub_fn_name(&mut self, name: &str) {
        self.cur_mod_ctx_mut().pub_fn_names.insert(name.to_string());
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
                let a_symbol = ASymbol::from(self, &symbol, true, true, true, false);

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
                    self.type_is_pub(a_symbol.type_key)
                } else {
                    mod_ctx.pub_fn_names.contains(symbol.name.as_str())
                };

                if !is_pub {
                    self.insert_err(AnalyzeError::new(
                        ErrorKind::UseOfPrivateValue,
                        format_code!("{} is not public", symbol.name).as_str(),
                        &symbol,
                    ));
                }

                // Define the symbol in the program context.
                if a_symbol.is_type {
                    match self.type_store.get_type(a_symbol.type_key) {
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
                    let scoped_symbol = ScopedSymbol::new_const(
                        symbol.name.as_str(),
                        a_symbol.type_key,
                        used_mod.path.raw.clone(),
                    );
                    self.insert_scoped_symbol(scoped_symbol);
                }
            }
        }
    }

    /// Returns the type key associated with the current `impl` or `spec` type being analyzed.
    pub fn get_cur_self_type_key(&self) -> Option<TypeKey> {
        self.cur_mod_ctx().cur_self_type_key
    }

    /// Returns the type key of the spec being implemented in the current `impl` or `spec`
    /// block, if any.
    pub fn get_cur_spec_type_key(&self) -> Option<TypeKey> {
        self.cur_mod_ctx().cur_spec_type_key
    }

    /// Inserts the given mapping from member function name to type key into the program context
    /// as an impl. If `maybe_spec_type_key` is not None, then it will be recorded as a spec impl
    /// for the given type.
    pub fn insert_impl(
        &mut self,
        type_key: TypeKey,
        maybe_spec_type_key: Option<TypeKey>,
        fns: HashMap<String, TypeKey>,
    ) {
        match self.type_impls.get_mut(&type_key) {
            Some(impls) => {
                impls.insert_impl(maybe_spec_type_key, fns);
            }

            None => {
                let mut impls = TypeImpls::new();
                impls.insert_impl(maybe_spec_type_key, fns);
                self.type_impls.insert(type_key, impls);
            }
        }
    }

    /// Returns the type key of the spec that the given function on the given implements.
    pub fn get_spec_impl_by_fn(&self, fn_type_key: TypeKey) -> Option<TypeKey> {
        let func = self.get_type(fn_type_key).to_fn_sig();
        match func.maybe_impl_type_key {
            Some(impl_tk) => match self.type_impls.get(&impl_tk) {
                Some(impls) => impls.get_spec_type_key(fn_type_key),
                // If there is no type impl, then maybe the function's impl type is a spec.
                // This can happen in cases where the function is actually a method on a generic
                // type declared as a parameter that implements a spec.
                None => match self.get_type(impl_tk).is_spec() {
                    true => Some(impl_tk),
                    false => None,
                },
            },
            None => None,
        }
    }

    /// Tries to locate (or generate) the member function with the given name on the given type.
    /// Returns:
    ///  - `Ok(Some(fn_sig))` if we found exactly one matching function on the type
    ///  - `Ok(None)` if we found no matching functions were found on the type
    ///  - `Err(tks)` if we found many matching functions on the type
    pub fn get_or_monomorphize_member_fn(
        &mut self,
        type_key: TypeKey,
        fn_name: &str,
    ) -> Result<Option<AFnSig>, HashSet<TypeKey>> {
        let fn_tks = self.get_member_fns(type_key, fn_name);
        match fn_tks.len() {
            // We didn't find any member functions for this type, but maybe this type was generated
            // as the result of a monomorphization and we have yet to generate this member function
            // for it. Let's check...
            0 => self.try_monomorphize_member_fn(type_key, fn_name),

            // Exactly one function by that name was found for the type. This is the ideal case.
            1 => {
                let tk = fn_tks.iter().next().unwrap();
                let fn_sig = self.get_type(*tk).to_fn_sig();
                Ok(Some(fn_sig.clone()))
            }

            // Many functions were found by that name.
            _ => Err(fn_tks),
        }
    }

    /// Tries to locate member functions with the given name on the given type. If the type
    /// implements multiple specs with methods that share the same name, then this function will
    /// return the type keys of all of those functions.
    fn get_member_fns(&self, type_key: TypeKey, fn_name: &str) -> HashSet<TypeKey> {
        match self.type_impls.get(&type_key) {
            Some(impls) => impls.get_fns_by_name(fn_name),
            None => HashSet::new(),
        }
    }

    /// Returns the type key of the default function on the given type with the given name, or
    /// None if no such function exists.
    pub fn get_default_member_fn(&self, type_key: TypeKey, fn_name: &str) -> Option<TypeKey> {
        match self.type_impls.get(&type_key) {
            Some(impls) => impls.get_default_fn(fn_name),
            None => None,
        }
    }

    /// Tries to find a function named `fn_name` that is a member of the given type that forms
    /// part of the implementation of the given spec.
    pub fn get_member_fn_from_spec_impl(
        &self,
        type_key: TypeKey,
        spec_tk: TypeKey,
        fn_name: &str,
    ) -> Option<TypeKey> {
        let type_impls = match self.type_impls.get(&type_key) {
            Some(impls) => impls,
            None => return None,
        };

        type_impls.get_fn_from_spec_impl(spec_tk, fn_name)
    }

    /// Tries to locate the given member function on the parent polymorphic type and monomorphizes
    /// it, if found.
    fn try_monomorphize_member_fn(
        &mut self,
        type_key: TypeKey,
        fn_name: &str,
    ) -> Result<Option<AFnSig>, HashSet<TypeKey>> {
        // Check if the given type is the result of a monomorphization. If not, then we're not
        // going to find the function so we can abort early.
        let mono = match self.type_monomorphizations.get(&type_key) {
            Some(mono) => mono.clone(),
            None => return Ok(None),
        };

        // Try to find the function by name on the parent polymorphic type.
        let poly_fn_tks = self.get_member_fns(mono.poly_type_key, fn_name);
        let poly_fn_tk = match poly_fn_tks.len() {
            // No function found.
            0 => return Ok(None),
            // Exactly one function found. This is what we want.
            1 => *poly_fn_tks.iter().next().unwrap(),
            // Many functions found by that name. We can't proceed because of this ambiguity.
            _ => return Err(poly_fn_tks),
        };

        let is_pub = self.member_fn_is_pub(mono.poly_type_key, poly_fn_tk);

        // Monomorphize the function from the polymorphic parent type.
        let type_mappings = mono.type_mappings();
        let mono_fn_sig = match self.monomorphize_fn_type(poly_fn_tk, &type_mappings) {
            Some(fn_tk) => self.get_type(fn_tk).to_fn_sig().clone(),
            // Monomorphization failed.
            None => return Ok(None),
        };

        // Figure out if this function was implemented as part of a spec. If so, we need to
        // associate the newly-monomorphized function with that same spec.
        let maybe_spec_tk = self
            .type_impls
            .get(&mono.poly_type_key)
            .unwrap()
            .get_spec_type_key(poly_fn_tk);

        self.insert_member_fn(type_key, maybe_spec_tk, mono_fn_sig.clone());
        if is_pub {
            self.mark_member_fn_pub(type_key, mono_fn_sig.type_key);
        }

        Ok(Some(mono_fn_sig))
    }

    /// Records the given member function as public in the program context.
    pub fn mark_member_fn_pub(&mut self, type_key: TypeKey, fn_type_key: TypeKey) {
        self.type_impls
            .get_mut(&type_key)
            .expect(format!("type with key {type_key} should have impls").as_str())
            .mark_fn_pub(fn_type_key);
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
        self.type_declared_in_cur_mod(type_key) || self.struct_field_is_pub(type_key, field_name)
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
    pub fn member_fn_is_accessible(&self, type_key: TypeKey, fn_type_key: TypeKey) -> bool {
        self.type_declared_in_cur_mod(type_key) || self.member_fn_is_pub(type_key, fn_type_key)
    }

    /// Returns true if the func with the given name from the given module is public.
    pub fn fn_is_pub(&self, mod_name: &String, name: &str) -> bool {
        let mod_ctx = self.get_mod_ctx(Some(mod_name));
        mod_ctx.pub_fn_names.contains(name)
    }

    /// Returns true if the constant with the given name from the given module is public.
    pub fn const_is_pub(&self, mod_name: &String, name: &str) -> bool {
        let mod_ctx = self.get_mod_ctx(Some(mod_name));
        mod_ctx.pub_const_names.contains(name)
    }

    /// Returns true if the given type was declared in the current module.
    pub fn type_declared_in_cur_mod(&self, type_key: TypeKey) -> bool {
        match self.type_declaration_mods.get(&type_key) {
            Some(mod_path) => mod_path == &self.cur_mod_path,
            None => false,
        }
    }

    /// Returns true if the given type member function is public.
    fn member_fn_is_pub(&self, type_key: TypeKey, fn_type_key: TypeKey) -> bool {
        // Generic types always have public member fns.
        if self.get_type(type_key).is_generic() {
            return true;
        }

        match self.type_impls.get(&type_key) {
            Some(impls) => impls.pub_fn_tks.contains(&fn_type_key),
            None => false,
        }
    }

    /// Inserts `member_fn_sig` as a member function on the type that corresponds to `type_key`.
    pub fn insert_member_fn(
        &mut self,
        type_key: TypeKey,
        maybe_spec_type_key: Option<TypeKey>,
        member_fn_sig: AFnSig,
    ) {
        match self.type_impls.get_mut(&type_key) {
            Some(impls) => {
                impls.insert_fn(
                    maybe_spec_type_key,
                    member_fn_sig.name,
                    member_fn_sig.type_key,
                );
            }
            None => {
                self.insert_impl(
                    type_key,
                    maybe_spec_type_key,
                    HashMap::from([(member_fn_sig.name, member_fn_sig.type_key)]),
                );
            }
        }
    }

    /// Returns the un-analyzed struct type with the given name.
    pub fn get_unchecked_struct_type(&self, name: &str) -> Option<&StructType> {
        self.cur_mod_ctx().unchecked_struct_types.get(name)
    }

    /// Returns the un-analyzed enum type with the given name.
    pub fn get_unchecked_enum_type(&self, name: &str) -> Option<&EnumType> {
        self.cur_mod_ctx().unchecked_enum_types.get(name)
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

    /// Changes the mangled type name in the given `mangled_name` to the mangled type name
    /// corresponding to `type_key`.
    pub fn remangle_name(&self, mangled_name: &str, type_key: TypeKey) -> String {
        mangling::remangle_type_in_name(&self.type_store, mangled_name, type_key)
    }

    /// Returns a name mangled to the following form.
    ///
    ///     <mod_path>::<type_prefix><spec_prefix><path><name>
    ///
    /// where
    ///  - `mod_path` is the full path of the module in which the symbol is
    ///    defined (determined by `maybe_mod_name`)
    ///  - `type_prefix` has the form `<type>.` if there is an impl type on
    ///    the function (determined by `maybe_impl_type_key`), or is empty
    ///  - `spec_prefix` has the form `impl:<spec>.` if the function implements a
    ///    spec (determined by `maybe_spec_type_key`), or is empty
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
        maybe_spec_type_key: Option<TypeKey>,
        name: &str,
        include_path: bool,
    ) -> String {
        let mod_ctx = self.cur_mod_ctx();
        let mod_path = match maybe_mod_name {
            Some(name) => mod_ctx.imported_mod_paths.get(name).unwrap(),
            None => self.cur_mod_path.as_str(),
        };

        // Get a path to the function based on the current scope.
        let mut fn_path = "".to_string();
        if include_path && !mod_ctx.fn_scope_indices.is_empty() {
            for i in &mod_ctx.fn_scope_indices {
                let fn_name = match &mod_ctx.stack.get(*i).unwrap().kind {
                    ScopeKind::FnBody(name) => name.as_str(),
                    _ => unreachable!(),
                };
                fn_path = fn_path + fn_name + "::";
            }
        }

        mangling::mangle_name(
            &self.type_store,
            mod_path,
            maybe_impl_type_key,
            maybe_spec_type_key,
            fn_path.as_str(),
            name,
        )
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
    pub fn insert_scoped_symbol(&mut self, symbol: ScopedSymbol) -> Option<ScopedSymbol> {
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
    pub fn insert_fn(&mut self, sig: AFnSig) {
        self.cur_mod_ctx_mut()
            .funcs
            .insert(sig.mangled_name.clone(), sig);
    }

    /// Tries to locate and return the signature of the function with the given full name in the
    /// current module context.
    pub fn get_fn(&self, maybe_mod_name: Option<&String>, name: &str) -> Option<&AFnSig> {
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
        let mangled_name = self.mangle_name(maybe_mod_name, None, None, name, false);
        if let Some(tk) = mod_ctx.struct_type_keys.get(mangled_name.as_str()) {
            return Some(self.get_type(*tk).to_struct_type());
        }

        None
    }

    /// Returns the enum type with the given name in the given module.
    pub fn get_enum_type(&self, maybe_mod_name: Option<&String>, name: &str) -> Option<&AEnumType> {
        let mod_ctx = self.get_mod_ctx(maybe_mod_name);
        if let Some(tk) = mod_ctx.enum_type_keys.get(name) {
            return Some(self.get_type(*tk).to_enum_type());
        }

        None
    }

    /// Returns the spec type with the given name in the given module.
    pub fn get_spec_type(&self, maybe_mod_name: Option<&String>, name: &str) -> Option<&ASpecType> {
        let mod_ctx = self.get_mod_ctx(maybe_mod_name);
        if let Some(tk) = mod_ctx.spec_type_keys.get(name) {
            return Some(self.get_type(*tk).to_spec_type());
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
        let typ = self.get_type(type_key);
        match typ {
            AType::Bool
            | AType::Str
            | AType::Char
            | AType::I8
            | AType::U8
            | AType::I16
            | AType::U16
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

            AType::Spec(spec_type) => {
                format!("{}{}", spec_type.name, self.display_param_types(type_key))
            }

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

            AType::Function(fn_sig) => fn_sig.display(self),

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
                // Prevent infinite recursion.
                let param_display = if replaced_param.replacement_type_key == type_key {
                    self.display_type(replaced_param.param_type_key)
                } else {
                    self.display_type(replaced_param.replacement_type_key)
                };

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
