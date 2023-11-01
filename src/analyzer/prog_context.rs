use std::collections::hash_map::Iter;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

use crate::analyzer::arg::RichArg;
use crate::analyzer::error::AnalyzeError;
use crate::analyzer::error::AnalyzeResult;
use crate::analyzer::func::RichFn;
use crate::analyzer::func_sig::RichFnSig;
use crate::analyzer::r#enum::RichEnumType;
use crate::analyzer::r#spec::RichSpec;
use crate::analyzer::r#struct::RichStructType;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::analyzer::statement::RichStatement;
use crate::analyzer::tmpl_params::RichTmplParam;
use crate::analyzer::warn::AnalyzeWarning;
use crate::lexer::pos::Position;
use crate::parser::func::Function;
use crate::parser::r#enum::EnumType;
use crate::parser::r#struct::StructType;
use crate::parser::spec::Spec;

/// Represents a symbol defined in a specific scope.
#[derive(Clone)]
pub struct ScopedSymbol {
    pub name: String,
    pub type_id: TypeId,
    pub is_mut: bool,
    pub is_arg: bool,
    pub is_const: bool,
}

impl ScopedSymbol {
    pub fn new(name: &str, type_id: TypeId, is_mut: bool, is_arg: bool) -> Self {
        ScopedSymbol {
            name: name.to_string(),
            type_id,
            is_mut,
            is_arg,
            is_const: false,
        }
    }

    pub fn new_const(name: &str, type_id: TypeId) -> Self {
        ScopedSymbol {
            name: name.to_string(),
            type_id,
            is_mut: false,
            is_arg: false,
            is_const: true,
        }
    }
}

/// Represents a kind of scope in which symbols can be defined.
#[derive(PartialEq, Clone, Debug)]
pub enum ScopeKind {
    FnBody,
    Inline,
    Branch,
    Loop,
    Tmpl,
}

impl fmt::Display for ScopeKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ScopeKind::FnBody => write!(f, "function body"),
            ScopeKind::Inline => write!(f, "inline closure"),
            ScopeKind::Branch => write!(f, "branch body"),
            ScopeKind::Loop => write!(f, "loop body"),
            ScopeKind::Tmpl => write!(f, "template"),
        }
    }
}

/// Represents a scope in the program. Each scope corresponds to a unique closure which can
/// be a function body, an inline closure, a branch, or a loop.
pub struct Scope {
    symbols: HashMap<String, ScopedSymbol>,
    /// Extern functions are functions that are defined outside the program and linked to it
    /// after compilation.
    extern_fns: HashMap<String, RichFnSig>,
    fns: HashMap<String, RichFn>,
    /// Extern structs are structs that have been detected but not yet analyzed.
    extern_structs: HashMap<String, StructType>,
    /// Extern enums are enums that have been detected but not yet analyzed.
    extern_enums: HashMap<String, EnumType>,
    structs: HashMap<String, RichStructType>,
    enums: HashMap<String, RichEnumType>,
    /// Invalid types are types that failed semantic analysis.
    invalid_types: HashSet<String>,
    resolved_types: HashMap<TypeId, RichType>,
    kind: ScopeKind,
    return_type: Option<TypeId>,
    /// Tracks type IDs that should be remapped before being resolved to concrete types. This is
    /// used for type replacement in templated types and functions.
    remapped_type_ids: HashMap<TypeId, TypeId>,
}

impl Scope {
    /// Creates a new scope.
    pub fn new(kind: ScopeKind, args: Vec<RichArg>, return_type: Option<TypeId>) -> Self {
        // If there are args, add them to the current scope symbols.
        let mut symbols = HashMap::new();
        for arg in args {
            symbols.insert(
                arg.name.clone(),
                ScopedSymbol::new(arg.name.as_str(), arg.type_id, arg.is_mut, true),
            );
        }

        Scope {
            symbols,
            extern_fns: HashMap::new(),
            fns: HashMap::new(),
            extern_structs: HashMap::new(),
            extern_enums: HashMap::new(),
            structs: HashMap::new(),
            enums: HashMap::new(),
            invalid_types: HashSet::new(),
            resolved_types: HashMap::new(),
            kind,
            return_type,
            remapped_type_ids: HashMap::new(),
        }
    }

    /// Creates a new template scope (a scope in which some types may be templated).
    pub fn new_tmpl(tmpl_params: Vec<RichTmplParam>, return_type: Option<TypeId>) -> Self {
        let mut resolved_types = HashMap::new();
        for param in &tmpl_params {
            resolved_types.insert(param.get_type_id(), RichType::Templated(param.clone()));
        }

        Scope {
            symbols: Default::default(),
            extern_fns: Default::default(),
            fns: Default::default(),
            extern_structs: Default::default(),
            extern_enums: Default::default(),
            structs: Default::default(),
            enums: Default::default(),
            invalid_types: Default::default(),
            resolved_types,
            kind: ScopeKind::Tmpl,
            return_type,
            remapped_type_ids: HashMap::new(),
        }
    }

    /// Adds the given name to the set of invalid types in the scope. Returns true if the scope did
    /// not already contain the invalid type and false otherwise.
    fn add_invalid_type(&mut self, name: &str) -> bool {
        self.invalid_types.insert(name.to_string())
    }

    /// Adds the mapping from type ID to resolved type to the scope and returns the old type
    /// that used to correspond to `id`, if one exists.
    fn add_resolved_type(&mut self, id: TypeId, resolved: RichType) -> Option<RichType> {
        self.resolved_types.insert(id, resolved)
    }

    /// Removes the type corresponding to `id` from the scope and returns it, if found.
    fn remove_resolved_type(&mut self, id: &TypeId) -> Option<RichType> {
        self.resolved_types.remove(id)
    }

    // Adds the signature of the external function to the scope. If there was already a function
    // with the same name in the scope, returns the old function. Use this method to record the
    // existence of functions before their bodies are analyzed.
    fn add_extern_fn(&mut self, sig: RichFnSig) -> Option<RichFnSig> {
        self.extern_fns.insert(sig.name.to_string(), sig)
    }

    // Returns the external function signature with the given name from the scope, or None if no
    // such external function exists.
    fn get_extern_fn(&self, name: &str) -> Option<&RichFnSig> {
        self.extern_fns.get(name)
    }

    // Adds the function to the scope. If there was already a function with the same name in the
    // scope, returns the old function.
    fn add_fn(&mut self, func: RichFn) -> Option<RichFn> {
        self.fns.insert(func.signature.name.to_string(), func)
    }

    // Adds the external struct type to the scope. If there was already a struct type with the same
    // name in the scope, returns the old type.
    fn add_extern_struct(&mut self, s: StructType) -> Option<StructType> {
        self.extern_structs.insert(s.name.to_string(), s)
    }

    // Adds the external enum type to the scope. If there was already a enum type with the same
    // name in the scope, returns the old type.
    fn add_extern_enum(&mut self, e: EnumType) -> Option<EnumType> {
        self.extern_enums.insert(e.name.to_string(), e)
    }

    /// Removes the extern struct type with the given name from the scope.
    pub fn remove_extern_struct(&mut self, name: &str) {
        self.extern_structs.remove(name);
    }

    /// Removes the extern enum type with the given name from the scope.
    pub fn remove_extern_enum(&mut self, name: &str) {
        self.extern_enums.remove(name);
    }

    // Adds the struct type to the scope. If there was already a struct type with the same name in
    // the scope, returns the old type.
    fn add_struct(&mut self, s: RichStructType) -> Option<RichStructType> {
        self.structs.insert(s.name.to_string(), s)
    }

    // Adds the enum type to the scope. If there was already a enum type with the same name in
    // the scope, returns the old type.
    fn add_enum(&mut self, e: RichEnumType) -> Option<RichEnumType> {
        self.enums.insert(e.name.to_string(), e)
    }

    // Adds the symbol to the scope. If there was already a symbol with the same name in
    // the scope, returns the old symbol.
    fn add_symbol(&mut self, symbol: ScopedSymbol) -> Option<ScopedSymbol> {
        self.symbols.insert(symbol.name.clone(), symbol)
    }

    /// Adds a mapping from `src_type_id` to `dst_type_id`.
    fn add_remapped_type_id(&mut self, src_type_id: TypeId, dst_type_id: TypeId) {
        self.remapped_type_ids.insert(src_type_id, dst_type_id);
    }

    // Returns the invalid type with the given name from the scope, if it exists.
    fn get_invalid_type(&self, name: &str) -> Option<&String> {
        self.invalid_types.get(name)
    }

    /// Returns the resolved type corresponding to the type ID, if it exists.
    fn get_resolved_type(&self, id: &TypeId) -> Option<&RichType> {
        self.resolved_types.get(id)
    }

    // Returns the function with the given name from the scope, or None if no such function exists.
    fn get_fn(&self, name: &str) -> Option<&RichFn> {
        self.fns.get(name)
    }

    // Returns the extern struct type with the given name from the scope, or None if no such type
    // exists.
    fn get_extern_struct(&self, name: &str) -> Option<&StructType> {
        self.extern_structs.get(name)
    }

    // Returns the extern enum type with the given name from the scope, or None if no such type
    // exists.
    fn get_extern_enum(&self, name: &str) -> Option<&EnumType> {
        self.extern_enums.get(name)
    }

    /// Returns an iterator over all extern structs in this scope.
    fn extern_structs(&self) -> Iter<String, StructType> {
        self.extern_structs.iter()
    }

    /// Returns an iterator over all extern enums in this scope.
    fn extern_enums(&self) -> Iter<String, EnumType> {
        self.extern_enums.iter()
    }

    // Returns the struct type with the given name from the scope, or None if no such type exists.
    fn get_struct(&self, name: &str) -> Option<&RichStructType> {
        self.structs.get(name)
    }

    // Returns the enum type with the given name from the scope, or None if no such type exists.
    fn get_enum(&self, name: &str) -> Option<&RichEnumType> {
        self.enums.get(name)
    }

    // Returns the symbol with the given name from the scope, or None if no such symbol
    // exists.
    fn get_symbol(&self, name: &str) -> Option<&ScopedSymbol> {
        self.symbols.get(name)
    }

    /// Attempts to locate the remapped type ID corresponding to `src_type_id`.
    fn get_remapped_type_id(&self, src_type_id: &TypeId) -> Option<&TypeId> {
        self.remapped_type_ids.get(src_type_id)
    }
}

/// Represents the current program stack and analysis state.
pub struct ProgramContext {
    stack: VecDeque<Scope>,
    /// The type ID that instances of the type `This` will resolve to.
    cur_this_type_id: Option<TypeId>,
    errors: HashMap<Position, AnalyzeError>,
    warnings: HashMap<Position, AnalyzeWarning>,
    /// Maps type IDs to mappings of member function name to member function signature.
    type_member_fn_sigs: HashMap<TypeId, HashMap<String, RichFnSig>>,
    /// Tracks specs that have not yet been analyzed.
    extern_specs: HashMap<String, Spec>,
    /// Stores all resolved types.
    pub types: HashMap<TypeId, RichType>,
    specs: HashMap<String, RichSpec>,
    templated_fns: HashMap<String, Function>,
    /// Contains functions that were templated but have been rendered.
    rendered_fns: Vec<RichFn>,
    /// Tracks the indices of all the scopes with `ScopeKind::Tmpl`. This is just used to make
    /// finding and accessing template scopes fast and easy.
    tmpl_scope_indices: Vec<usize>,
}

impl ProgramContext {
    /// Returns a new ProgramContext with a single initialized scope representing the global
    /// scope.
    pub fn new() -> Self {
        // Initialize the top-level scope with already-resolved primitive types so we can avoid
        // having to resolve them again.
        let mut top_scope = Scope::new(ScopeKind::Inline, vec![], None);
        for (type_id, typ) in RichType::primitives() {
            top_scope.add_resolved_type(type_id, typ);
        }

        ProgramContext {
            stack: VecDeque::from([top_scope]),
            cur_this_type_id: None,
            errors: HashMap::new(),
            warnings: HashMap::new(),
            type_member_fn_sigs: HashMap::new(),
            extern_specs: HashMap::new(),
            types: HashMap::new(),
            specs: HashMap::new(),
            templated_fns: HashMap::new(),
            rendered_fns: vec![],
            tmpl_scope_indices: vec![],
        }
    }

    /// Visits each stack in the scope in reverse, calling `visit` on each one until one of the
    /// following occurs
    /// - `visit` returns `Some`
    /// - a template rendering scope has been reached (in this case the template scope and the
    ///   top-level scope will be searched before returning)
    /// - the entire stack has been searched.
    /// Returns the value returned by the last call to `visit`.
    fn reverse_search_stack<F, R>(&self, visit: F) -> Option<&R>
    where
        F: Fn(&Scope) -> Option<&R>,
    {
        for scope in self.stack.iter().rev() {
            if let Some(result) = visit(scope) {
                return Some(result);
            }

            // Don't search beyond template rendering boundaries. If we didn't do this, types and
            // functions rendered where they're used would be able to access types and variables
            // declared in the context where they're used, which would be broken.
            if scope.kind == ScopeKind::Tmpl {
                // Visit the top level of the program before returning, as types and functions
                // declared there should be accessible everywhere.
                return visit(self.stack.front().unwrap());
            }
        }

        None
    }

    /// Works the same way as `reverse_search_stack`, except that this function returns when
    /// `visit` returns `(_, true)` rather than `Some` as in `reverse_search_stack`.
    fn reverse_search_stack_until<F, R>(&self, visit: F) -> Option<R>
    where
        F: Fn(&Scope) -> (Option<R>, bool),
    {
        for scope in self.stack.iter().rev() {
            let (result, stop) = visit(scope);
            if stop {
                return result;
            }
        }

        None
    }

    /// Gets the current template scope from the stack.
    fn get_cur_tmpl_scope(&self) -> Option<&Scope> {
        if let Some(index) = self.tmpl_scope_indices.last() {
            return self.stack.get(*index);
        }

        None
    }

    /// Gets a mutable reference to the current template scope from the stack.
    fn get_cur_tmpl_scope_mut(&mut self) -> Option<&mut Scope> {
        if let Some(index) = self.tmpl_scope_indices.last() {
            return self.stack.get_mut(*index);
        }

        None
    }

    /// Remaps `src_type_id` to a new type ID if it should be remapped (based on whether there is
    /// a template scope in the stack that remaps `src_type_id`. Returns `src_type_id` if the type
    /// ID doesn't need to be remapped.
    fn maybe_remap_type_id<'a>(&'a self, src_type_id: &'a TypeId) -> &TypeId {
        if let Some(scope) = self.get_cur_tmpl_scope() {
            if let Some(new_type_id) = scope.get_remapped_type_id(src_type_id) {
                return new_type_id;
            }
        }

        src_type_id
    }

    /// Returns all type mappings store in the program context.
    pub fn types(mut self) -> HashMap<TypeId, RichType> {
        // Make sure we move all type mappings from any existing scopes.
        loop {
            match self.stack.pop_back() {
                Some(scope) => {
                    self.types.extend(scope.resolved_types);
                }
                None => break,
            }
        }

        self.types
    }

    /// Returns all errors that have occurred during semantic analysis in ascending order of
    /// position (line and col) in the program.
    pub fn errors(&self) -> Vec<AnalyzeError> {
        let mut errors: Vec<(&Position, AnalyzeError)> =
            self.errors.iter().map(|(p, e)| (p, e.clone())).collect();
        errors.sort_by(|(pos1, _), (pos2, _)| pos1.cmp(pos2));
        errors.into_iter().map(|(_, e)| e).collect()
    }

    /// If the given result is an error, consumes and stores the error, returning None. Otherwise,
    /// returns the result.
    pub fn consume_error<T>(&mut self, result: AnalyzeResult<T>) -> Option<T> {
        match result {
            Ok(v) => Some(v),
            Err(e) => {
                self.add_err(e);
                None
            }
        }
    }

    /// Add the given error to the program context.
    pub fn add_err(&mut self, err: AnalyzeError) {
        self.errors.insert(err.start_pos.clone(), err);
    }

    /// Returns all warnings that have occurred during semantic analysis.
    pub fn warnings(&self) -> Vec<AnalyzeWarning> {
        let mut warnings = vec![];
        for mapping in &self.warnings {
            warnings.push(mapping);
        }
        warnings.sort_by(|(pos1, _), (pos2, _)| pos1.cmp(&pos2));
        warnings.into_iter().map(|(_, w)| w.clone()).collect()
    }

    /// Add the given warning to the program context.
    pub fn add_warn(&mut self, warn: AnalyzeWarning) {
        self.warnings.insert(warn.start_pos.clone(), warn);
    }

    /// Adds the given name to the set of invalid types in the program context. Returns true if
    /// the program context did not already contain this invalid type and false otherwise.
    pub fn add_invalid_type(&mut self, name: &str) -> bool {
        self.stack.back_mut().unwrap().add_invalid_type(name)
    }

    /// Adds the given mapping from type ID to resolved type to current scope in the program
    /// context and returns the old type that used to correspond to `id`, if one exists.
    pub fn add_resolved_type(&mut self, id: TypeId, resolved: RichType) -> Option<RichType> {
        self.stack
            .back_mut()
            .unwrap()
            .add_resolved_type(id, resolved)
    }

    /// Adds the given type mapping to the top level scope in the program context. This should only
    /// be used for templated types that have been rendered.
    pub fn add_rendered_type(&mut self, id: TypeId, resolved: RichType) -> Option<RichType> {
        self.stack
            .front_mut()
            .unwrap()
            .add_resolved_type(id, resolved)
    }

    /// Removes the resolved type that corresponds to `id` from the current scope only and returns
    /// it, if found.
    pub fn remove_resolved_type(&mut self, id: &TypeId) -> Option<RichType> {
        self.stack.back_mut().unwrap().remove_resolved_type(id)
    }

    /// Adds the member function signature `mem_fn_sig` to the given type in the program context.
    /// Returns the existing member function signature if it has the type name and parent type as
    /// (i.e. collides with) `mem_fn_sig`.
    pub fn add_type_member_fn(&mut self, id: TypeId, mem_fn_sig: RichFnSig) -> Option<RichFnSig> {
        match self.type_member_fn_sigs.get_mut(&id) {
            Some(mem_fns) => mem_fns.insert(mem_fn_sig.name.clone(), mem_fn_sig),
            None => {
                self.type_member_fn_sigs
                    .insert(id, HashMap::from([(mem_fn_sig.name.clone(), mem_fn_sig)]));
                None
            }
        }
    }

    /// Adds the external function signature to the top level of the program context. If there was
    /// already a function with the same name, returns the old function signature.
    pub fn add_extern_fn(&mut self, sig: RichFnSig) -> Option<RichFnSig> {
        self.stack.front_mut().unwrap().add_extern_fn(sig)
    }

    /// Adds the function to the context. If there was already a function with the same name,
    /// returns the old function.
    pub fn add_fn(&mut self, func: RichFn) -> Option<RichFn> {
        self.stack.back_mut().unwrap().add_fn(func)
    }

    /// Adds the external struct type to the context. If there was already a struct type with the
    /// same name, returns the old type.
    pub fn add_extern_struct(&mut self, s: StructType) -> Option<StructType> {
        self.stack.back_mut().unwrap().add_extern_struct(s)
    }

    /// Adds the external enum type to the context. If there was already a enum type with the
    /// same name, returns the old type.
    pub fn add_extern_enum(&mut self, s: EnumType) -> Option<EnumType> {
        self.stack.back_mut().unwrap().add_extern_enum(s)
    }

    /// Adds the given un-analyzed spec to the program context.
    pub fn add_extern_spec(&mut self, spec: Spec) -> Option<Spec> {
        self.extern_specs.insert(spec.name.clone(), spec)
    }

    /// Removes the extern struct type with the given name from the program context.
    pub fn remove_extern_struct(&mut self, name: &str) {
        self.stack.back_mut().unwrap().remove_extern_struct(name);
    }

    /// Removes the extern enum type with the given name from the program context.
    pub fn remove_extern_enum(&mut self, name: &str) {
        self.stack.back_mut().unwrap().remove_extern_enum(name);
    }

    /// Adds the struct type to the context. If there was already a struct type with the same name,
    /// returns the old type.
    pub fn add_struct(&mut self, s: RichStructType) -> Option<RichStructType> {
        self.stack.back_mut().unwrap().add_struct(s)
    }

    /// Adds the enum type to the context. If there was already a enum type with the same name,
    /// returns the old type.
    pub fn add_enum(&mut self, e: RichEnumType) -> Option<RichEnumType> {
        self.stack.back_mut().unwrap().add_enum(e)
    }

    /// Adds the symbol type ID to the context. If there was already a symbol with the same
    /// name, returns the old symbol type ID.
    pub fn add_symbol(&mut self, symbol: ScopedSymbol) -> Option<ScopedSymbol> {
        self.stack.back_mut().unwrap().add_symbol(symbol)
    }

    /// Adds `spec_` to the program context. Returns an existing spec if its name matches that of
    /// `spec_`.
    pub fn add_spec(&mut self, spec_: RichSpec) -> Option<RichSpec> {
        self.specs.insert(spec_.name.clone(), spec_)
    }

    /// Attempts to locate the invalid type with the given name and returns it, if found.
    pub fn get_invalid_type(&self, name: &str) -> Option<&String> {
        self.reverse_search_stack(|scope| scope.get_invalid_type(name))
    }

    /// Attempts to locate the resolved type corresponding to the given type ID and returns it,
    /// if found.
    pub fn get_resolved_type(&self, id: &TypeId) -> Option<&RichType> {
        let id = self.maybe_remap_type_id(id);
        self.reverse_search_stack(|scope| scope.get_resolved_type(id))
    }

    /// Attempts to locate the resolved type corresponding to the given type ID and returns it,
    /// if found. Panics if the type is not found.
    pub fn must_get_resolved_type(&self, id: &TypeId) -> &RichType {
        match self.get_resolved_type(id) {
            Some(typ) => typ,
            None => panic!("type {} does not exist in the program context", id),
        }
    }

    /// Returns the member function with name `name` on the type with ID `id`, if one exists.
    pub fn get_type_member_fn(&self, id: &TypeId, name: &str) -> Option<&RichFnSig> {
        let id = self.maybe_remap_type_id(id);
        match self.type_member_fn_sigs.get(id) {
            Some(member_fns) => member_fns.get(name),
            None => None,
        }
    }

    /// Returns the mapping from member function name to member function signature for all member
    /// functions corresponding to the given type ID.
    pub fn get_type_member_fns(&self, id: &TypeId) -> Option<&HashMap<String, RichFnSig>> {
        let id = self.maybe_remap_type_id(id);
        self.type_member_fn_sigs.get(id)
    }

    /// Returns remapped type IDs for the current template rendering scope, or None if there is no
    /// current template rendering scope.
    pub fn get_remapped_type_ids(&mut self) -> Option<&mut HashMap<TypeId, TypeId>> {
        match self.get_cur_tmpl_scope_mut() {
            Some(scope) => Some(&mut scope.remapped_type_ids),
            None => None,
        }
    }

    /// Attempts to locate the external function signature with the given name and returns it,
    /// if found.
    pub fn get_extern_fn(&self, name: &str) -> Option<&RichFnSig> {
        self.reverse_search_stack(|scope| scope.get_extern_fn(name))
    }

    /// Attempts to locate the function with the given name and returns it, if found.
    pub fn get_fn(&self, name: &str) -> Option<&RichFn> {
        self.reverse_search_stack(|scope| scope.get_fn(name))
    }

    /// Attempts to locate the extern struct type with the given name and returns it, if found.
    pub fn get_extern_struct(&self, name: &str) -> Option<&StructType> {
        self.reverse_search_stack(|scope| scope.get_extern_struct(name))
    }

    /// Attempts to locate the extern enum type with the given name and returns it, if found.
    pub fn get_extern_enum(&self, name: &str) -> Option<&EnumType> {
        self.reverse_search_stack(|scope| scope.get_extern_enum(name))
    }

    /// Attempts to locate the un-analyzed spec with the given name.
    pub fn get_extern_spec(&self, name: &str) -> Option<&Spec> {
        self.extern_specs.get(name)
    }

    /// Attempts to locate the struct type with the given name and returns it, if found.
    pub fn get_struct(&self, name: &str) -> Option<&RichStructType> {
        self.reverse_search_stack(|scope| scope.get_struct(name))
    }

    /// Attempts to locate the enum type with the given name and returns it, if found.
    pub fn get_enum(&self, name: &str) -> Option<&RichEnumType> {
        self.reverse_search_stack(|scope| scope.get_enum(name))
    }

    /// Returns all extern structs in the program context.
    pub fn extern_structs(&self) -> Vec<&StructType> {
        let mut extern_structs = vec![];
        for scope in self.stack.iter() {
            for (_, struct_type) in scope.extern_structs() {
                extern_structs.push(struct_type);
            }
        }

        extern_structs
    }

    /// Returns all extern enums in the program context.
    pub fn extern_enums(&self) -> Vec<&EnumType> {
        let mut extern_enums = vec![];
        for scope in self.stack.iter() {
            for (_, struct_type) in scope.extern_enums() {
                extern_enums.push(struct_type);
            }
        }

        extern_enums
    }

    /// Attempts to locate the symbol with the given name and returns it, if found.
    pub fn get_symbol(&self, name: &str) -> Option<&ScopedSymbol> {
        self.reverse_search_stack(|scope| scope.get_symbol(name))
    }

    /// Returns the spec with the given name, or `None` if there is no such spec.
    pub fn get_spec(&self, name: &str) -> Option<&RichSpec> {
        self.specs.get(name)
    }

    /// Adds the given scope to the top of the stack.
    pub fn push_scope(&mut self, scope: Scope) {
        // Push the new template scope index onto the index stack so we can find with easily.
        if scope.kind == ScopeKind::Tmpl {
            self.tmpl_scope_indices.push(self.stack.len());
        }

        self.stack.push_back(scope);
    }

    /// Pops the scope at the top of the stack and copies all of its resolved types to the program
    /// context.
    pub fn pop_scope(&mut self) {
        let scope = self.stack.pop_back().unwrap();

        // If the scope was a template scope, we need to pop its index from the index stack since
        // it can no longer be found.
        if scope.kind == ScopeKind::Tmpl {
            self.tmpl_scope_indices.pop();
        }

        // Copy all types from the scope into the program context. We'll need them later.
        self.types.extend(scope.resolved_types);
    }

    /// Returns true if the current scope falls within a function body at any depth.
    pub fn is_in_fn(&self) -> bool {
        self.reverse_search_stack(|scope| match scope.kind == ScopeKind::FnBody {
            true => Some(&()),
            false => None,
        })
        .is_some()
    }

    /// Returns true if the current scope falls within a loop.
    pub fn is_in_loop(&self) -> bool {
        self.reverse_search_stack_until(|scope| match scope.kind {
            ScopeKind::Loop => (Some(()), true),
            ScopeKind::FnBody => (None, true),
            _ => (None, false),
        })
        .is_some()
    }

    /// Returns the return type ID of the current scope, or none if there is no return type.
    pub fn return_type(&self) -> &Option<TypeId> {
        let result = self.reverse_search_stack(|scope| match &scope.kind {
            ScopeKind::FnBody => Some(&scope.return_type),
            _ => None,
        });

        match result {
            Some(maybe_ret_type_id) => maybe_ret_type_id,
            None => &None,
        }
    }

    /// Sets the type ID that will correspond to the type `This`. In other words, after this is
    /// called, all instances of the type `This` will resolve to `maybe_type_id`.
    pub fn set_this_type_id(&mut self, maybe_type_id: Option<TypeId>) {
        self.cur_this_type_id = maybe_type_id;
    }

    /// Returns the type ID of the current `impl` or `spec` block, or `None` if we're not in an
    /// `impl` or `spec` block.
    pub fn get_this_type_id(&self) -> Option<&TypeId> {
        self.cur_this_type_id.as_ref()
    }

    /// Returns true if the given type or spec name has already been used.
    pub fn is_type_or_spec_name_used(&self, name: &str) -> bool {
        self.extern_specs.contains_key(name)
            || self.get_extern_struct(name).is_some()
            || self.get_extern_enum(name).is_some()
            || RichType::get_primitive(name).is_some()
    }

    /// Adds the given un-analyzed function to the program context. Note that `full_name` should
    /// be the fully-qualified name of the function.
    pub fn add_templated_fn(&mut self, full_name: &str, func: Function) {
        self.templated_fns.insert(full_name.to_string(), func);
    }

    /// Attempts to locate and return a templated function by the given name. Note that `full_name`
    /// should be the fully-qualified name of the function. Panics if the function is not found.
    pub fn must_get_templated_fn(&mut self, full_name: &str) -> &Function {
        match self.templated_fns.get(full_name) {
            Some(f) => f,
            None => panic!(
                "function {} does not exist in the program context",
                full_name
            ),
        }
    }

    /// Adds the given rendered function to the program context.
    pub fn add_rendered_fn(&mut self, rendered_fn: RichFn) {
        assert!(!rendered_fn.signature.is_templated());
        self.rendered_fns.push(rendered_fn);
    }

    /// Turns all rendered functions in the program context into statements and returns them.
    pub fn get_rendered_functions_as_statements(&self) -> Vec<RichStatement> {
        let mut statements = vec![];
        for func in &self.rendered_fns {
            statements.push(RichStatement::FunctionDeclaration(func.clone()));
        }

        statements
    }

    /// Remaps type ID `src_type_id` to `dst_type_id` in the program context so that every time
    /// any method on the program context sees `src_type_id`, it is translated into `dst_type_id`
    /// before it is used by the program context to look up other program info.
    pub fn add_type_id_remapping(&mut self, src_type_id: TypeId, dst_type_id: TypeId) {
        let scope = self.get_cur_tmpl_scope_mut().unwrap();
        scope.add_remapped_type_id(src_type_id, dst_type_id);
    }
}
