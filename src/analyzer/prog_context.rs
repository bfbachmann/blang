use crate::analyzer::arg::RichArg;
use std::collections::hash_map::Iter;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

use crate::analyzer::error::AnalyzeError;
use crate::analyzer::error::AnalyzeResult;
use crate::analyzer::func::RichFn;
use crate::analyzer::func_sig::RichFnSig;
use crate::analyzer::r#struct::RichStructType;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::analyzer::warn::AnalyzeWarning;
use crate::lexer::pos::Position;
use crate::parser::r#struct::StructType;

/// Represents a variable defined in a specific scope.
pub struct ScopedVar {
    pub name: String,
    pub type_id: TypeId,
    pub is_mut: bool,
    pub is_arg: bool,
    pub is_const: bool,
}

impl ScopedVar {
    pub fn new(name: &str, type_id: TypeId, is_mut: bool, is_arg: bool) -> Self {
        ScopedVar {
            name: name.to_string(),
            type_id,
            is_mut,
            is_arg,
            is_const: false,
        }
    }

    pub fn new_const(name: &str, type_id: TypeId) -> Self {
        ScopedVar {
            name: name.to_string(),
            type_id,
            is_mut: false,
            is_arg: false,
            is_const: true,
        }
    }
}

/// Represents a kind of scope in which variables can be defined.
#[derive(PartialEq, Clone)]
pub enum ScopeKind {
    FnBody,
    Inline,
    Branch,
    Loop,
}

impl fmt::Display for ScopeKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ScopeKind::FnBody => write!(f, "function body"),
            ScopeKind::Inline => write!(f, "inline closure"),
            ScopeKind::Branch => write!(f, "branch body"),
            ScopeKind::Loop => write!(f, "loop body"),
        }
    }
}

/// Represents a scope in the program. Each scope corresponds to a unique closure which can
/// be a function body, an inline closure, a branch, or a loop.
pub struct Scope {
    vars: HashMap<String, ScopedVar>,
    /// Extern functions are functions that are defined outside the program and linked to it
    /// after compilation.
    extern_fns: HashMap<String, RichFnSig>,
    fns: HashMap<String, RichFn>,
    /// Extern structs are structs that have been detected but not yet analyzed.
    extern_structs: HashMap<String, StructType>,
    structs: HashMap<String, RichStructType>,
    /// Invalid types are types that failed semantic analysis.
    invalid_types: HashSet<String>,
    resolved_types: HashMap<TypeId, RichType>,
    kind: ScopeKind,
    return_type: Option<TypeId>,
}

impl Scope {
    /// Creates a new scope.
    pub fn new(kind: ScopeKind, args: Vec<RichArg>, return_type: Option<TypeId>) -> Self {
        // If there are args, add them to the current scope variables.
        let mut vars = HashMap::new();
        for arg in args {
            vars.insert(
                arg.name.clone(),
                ScopedVar::new(arg.name.as_str(), arg.type_id, arg.is_mut, true),
            );
        }

        Scope {
            vars,
            extern_fns: HashMap::new(),
            fns: HashMap::new(),
            extern_structs: HashMap::new(),
            structs: HashMap::new(),
            invalid_types: HashSet::new(),
            resolved_types: HashMap::new(),
            kind,
            return_type,
        }
    }

    /// Adds the given name to the set of invalid types in the scope. Returns true if the scope did
    /// not already contain the invalid type and false otherwise.
    fn add_invalid_type(&mut self, name: &str) -> bool {
        self.invalid_types.insert(name.to_string())
    }

    /// Adds the mapping from type ID to resolved type to the scope.
    fn add_resolved_type(&mut self, id: TypeId, resolved: RichType) {
        self.resolved_types.insert(id, resolved);
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

    /// Removes the extern struct type with the given name from the scope.
    pub fn remove_extern_struct(&mut self, name: &str) {
        self.extern_structs.remove(name);
    }

    // Adds the struct type to the scope. If there was already a struct type with the same name in
    // the scope, returns the old type.
    fn add_struct(&mut self, s: RichStructType) -> Option<RichStructType> {
        self.structs.insert(s.name.to_string(), s)
    }

    // Adds the variable to the scope. If there was already a variable with the same name in
    // the scope, returns the old variable.
    fn add_var(&mut self, var: ScopedVar) -> Option<ScopedVar> {
        self.vars.insert(var.name.clone(), var)
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

    /// Returns an iterator over all extern structs in this scope.
    fn extern_structs(&self) -> Iter<String, StructType> {
        self.extern_structs.iter()
    }

    // Returns the struct type with the given name from the scope, or None if no such type exists.
    fn get_struct(&self, name: &str) -> Option<&RichStructType> {
        self.structs.get(name)
    }

    // Returns the variable with the given name from the scope, or None if no such variable
    // exists.
    fn get_var(&self, name: &str) -> Option<&ScopedVar> {
        self.vars.get(name)
    }
}

/// Represents the current program stack and analysis state.
pub struct ProgramContext {
    stack: VecDeque<Scope>,
    /// The type ID that corresponds to the current `impl` block, if we're inside an `impl` block.
    cur_impl_type_id: Option<TypeId>,
    errors: HashMap<Position, AnalyzeError>,
    warnings: HashMap<Position, AnalyzeWarning>,
    /// Maps type IDs to mappings of member function name to member function signature.
    type_member_fn_sigs: HashMap<TypeId, HashMap<String, RichFnSig>>,
    /// Stores all resolved types.
    pub types: HashMap<TypeId, RichType>,
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
            cur_impl_type_id: None,
            errors: HashMap::new(),
            warnings: HashMap::new(),
            type_member_fn_sigs: HashMap::new(),
            types: HashMap::new(),
        }
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
    /// context.
    pub fn add_resolved_type(&mut self, id: TypeId, resolved: RichType) {
        self.stack
            .back_mut()
            .unwrap()
            .add_resolved_type(id, resolved)
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

    /// Adds the external function signature to the context. If there was already a function with
    /// the same name, returns the old function signature.
    pub fn add_extern_fn(&mut self, sig: RichFnSig) -> Option<RichFnSig> {
        self.stack.back_mut().unwrap().add_extern_fn(sig)
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

    /// Removes the extern struct type with the given name from the program context.
    pub fn remove_extern_struct(&mut self, name: &str) {
        self.stack.back_mut().unwrap().remove_extern_struct(name);
    }

    /// Adds the struct type to the context. If there was already a struct type with the same name,
    /// returns the old type.
    pub fn add_struct(&mut self, s: RichStructType) -> Option<RichStructType> {
        self.stack.back_mut().unwrap().add_struct(s)
    }

    /// Adds the variable type ID to the context. If there was already a variable with the same
    /// name, returns the old variable type ID.
    pub fn add_var(&mut self, var: ScopedVar) -> Option<ScopedVar> {
        self.stack.back_mut().unwrap().add_var(var)
    }

    /// Attempts to locate the invalid type with the given name and returns it, if found.
    pub fn get_invalid_type(&self, name: &str) -> Option<&String> {
        // Search up the stack from the current scope.
        for scope in self.stack.iter().rev() {
            if let Some(sig) = scope.get_invalid_type(name) {
                return Some(sig);
            }
        }

        None
    }

    /// Attempts to locate the resolved type corresponding to the given type ID and returns it,
    /// if found.
    pub fn get_resolved_type(&self, id: &TypeId) -> Option<&RichType> {
        // Unlike with variable resolution, we're going to search the stack top-down here because
        // types are generally defined at the top level of the program, and type names cannot
        // collide like variable names.
        for scope in self.stack.iter() {
            if let Some(resolved) = scope.get_resolved_type(id) {
                return Some(resolved);
            }
        }

        None
    }

    /// Returns the member function with name `name` on the type with ID `id`, if one exists.
    pub fn get_type_member_fn(&self, id: &TypeId, name: &str) -> Option<&RichFnSig> {
        match self.type_member_fn_sigs.get(id) {
            Some(member_fns) => member_fns.get(name),
            None => None,
        }
    }

    /// Attempts to locate the external function signature with the given name and returns it,
    /// if found.
    pub fn get_extern_fn(&self, name: &str) -> Option<&RichFnSig> {
        // Search up the stack from the current scope.
        for scope in self.stack.iter().rev() {
            if let Some(sig) = scope.get_extern_fn(name) {
                return Some(sig);
            }
        }

        None
    }

    /// Attempts to locate the function with the given name and returns it, if found.
    pub fn get_fn(&self, name: &str) -> Option<&RichFn> {
        // Search up the stack from the current scope.
        for scope in self.stack.iter().rev() {
            if let Some(func) = scope.get_fn(name) {
                return Some(func);
            }
        }

        None
    }

    /// Attempts to locate the extern struct type with the given name and returns it, if found.
    pub fn get_extern_struct(&self, name: &str) -> Option<&StructType> {
        // Search up the stack from the current scope.
        for scope in self.stack.iter().rev() {
            if let Some(s) = scope.get_extern_struct(name) {
                return Some(s);
            }
        }

        None
    }

    /// Attempts to locate the struct type with the given name and returns it, if found.
    pub fn get_struct(&self, name: &str) -> Option<&RichStructType> {
        // Search up the stack from the current scope.
        for scope in self.stack.iter().rev() {
            if let Some(s) = scope.get_struct(name) {
                return Some(s);
            }
        }

        None
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

    /// Attempts to locate the variable with the given name and returns it, if found.
    pub fn get_var(&self, name: &str) -> Option<&ScopedVar> {
        // Search up the stack from the current scope.
        for scope in self.stack.iter().rev() {
            if let Some(var) = scope.get_var(name) {
                return Some(var);
            }
        }

        None
    }

    /// Adds the given scope to the top of the stack.
    pub fn push_scope(&mut self, scope: Scope) {
        self.stack.push_back(scope);
    }

    /// Pops the scope at the top of the stack and copies all of its resolved types to the program
    /// context.
    pub fn pop_scope(&mut self) {
        let scope = self.stack.pop_back().unwrap();

        // Copy all types from the scope into the program context. We'll need them later.
        self.types.extend(scope.resolved_types);
    }

    /// Returns true if the current scope falls within a function body at any depth.
    pub fn is_in_fn(&self) -> bool {
        // Search up the stack from the current scope to see if we are inside a function body.
        for scope in self.stack.iter().rev() {
            if scope.kind == ScopeKind::FnBody {
                return true;
            }
        }

        false
    }

    /// Returns true if the current scope falls within a loop.
    pub fn is_in_loop(&self) -> bool {
        for scope in self.stack.iter().rev() {
            if scope.kind == ScopeKind::Loop {
                return true;
            } else if scope.kind == ScopeKind::FnBody {
                return false;
            }
        }

        false
    }

    /// Returns the return type ID of the current scope, or none if there is no return type.
    pub fn return_type(&self) -> &Option<TypeId> {
        for scope in self.stack.iter().rev() {
            if scope.kind == ScopeKind::FnBody {
                return &scope.return_type;
            }
        }

        &None
    }

    /// Sets the type ID of the current `impl` block.
    pub fn set_impl_type_id(&mut self, maybe_type_id: Option<TypeId>) {
        self.cur_impl_type_id = maybe_type_id;
    }

    /// Returns the type ID of the current `impl` block, or `None` if we're not in an `impl` block.
    pub fn get_impl_type_id(&self) -> Option<&TypeId> {
        self.cur_impl_type_id.as_ref()
    }
}
