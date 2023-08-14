use std::collections::hash_map::Iter;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

use crate::analyzer::error::AnalyzeError;
use crate::analyzer::func::{RichArg, RichFn, RichFnSig};
use crate::analyzer::r#struct::RichStruct;
use crate::analyzer::r#type::RichType;
use crate::analyzer::warn::Warning;
use crate::analyzer::AnalyzeResult;
use crate::lexer::pos::Position;
use crate::parser::r#struct::StructType;

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
    vars: HashMap<String, RichType>,
    /// Extern functions are functions that are defined outside the program and linked to it
    /// after compilation.
    extern_fns: HashMap<String, RichFnSig>,
    fns: HashMap<String, RichFn>,
    /// Extern structs are structs that have been detected but not yet analyzed.
    extern_structs: HashMap<String, StructType>,
    structs: HashMap<String, RichStruct>,
    /// Invalid types are types that failed semantic analysis.
    invalid_types: HashSet<String>,
    kind: ScopeKind,
    return_type: Option<RichType>,
}

impl Scope {
    /// Creates a new scope.
    pub fn new(kind: ScopeKind, args: Vec<RichArg>, return_type: Option<RichType>) -> Self {
        // If there are args, add them to the current scope variables.
        let mut vars = HashMap::new();
        for arg in args {
            vars.insert(arg.name, arg.typ);
        }

        Scope {
            vars,
            extern_fns: HashMap::new(),
            fns: HashMap::new(),
            extern_structs: HashMap::new(),
            structs: HashMap::new(),
            invalid_types: HashSet::new(),
            kind,
            return_type,
        }
    }

    /// Adds the given name to the set of invalid types in the scope.
    fn add_invalid_type(&mut self, name: &str) -> bool {
        self.invalid_types.insert(name.to_string())
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
    fn add_struct(&mut self, s: RichStruct) -> Option<RichStruct> {
        self.structs.insert(s.name.to_string(), s)
    }

    // Adds the variable to the scope. If there was already a variable with the same name in the
    // scope, returns the old variable type.
    fn add_var(&mut self, name: &str, typ: RichType) -> Option<RichType> {
        self.vars.insert(name.to_string(), typ)
    }

    // Returns the invalid type with the given name from the scope, if it exists.
    fn get_invalid_type(&self, name: &str) -> Option<&String> {
        self.invalid_types.get(name)
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
    fn get_struct(&self, name: &str) -> Option<&RichStruct> {
        self.structs.get(name)
    }

    // Returns the variable with the given name from the scope, or None if no such variable exists.
    fn get_var(&self, name: &str) -> Option<&RichType> {
        self.vars.get(name)
    }
}

/// Represents the current program stack and analysis state.
pub struct ProgramContext {
    stack: VecDeque<Scope>,
    errors: HashMap<Position, AnalyzeError>,
    warnings: HashMap<Position, Warning>,
}

impl ProgramContext {
    /// Returns a new ProgramContext with a single initialized scope representing the global
    /// scope.
    pub fn new() -> Self {
        ProgramContext {
            stack: VecDeque::from([Scope::new(ScopeKind::Inline, vec![], None)]),
            errors: HashMap::new(),
            warnings: HashMap::new(),
        }
    }

    /// Returns all errors that have occurred during semantic analysis.
    pub fn errors(&self) -> Vec<AnalyzeError> {
        let mut errors: Vec<(Position, AnalyzeError)> = self
            .errors
            .iter()
            .map(|(p, e)| (p.clone(), e.clone()))
            .collect();
        errors.sort_by(|(pos1, _), (pos2, _)| pos1.cmp(pos2));
        errors.into_iter().map(|(_, err)| err).collect()
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
    pub fn warnings(self) -> Vec<Warning> {
        let mut warnings: Vec<(Position, Warning)> = self.warnings.into_iter().collect();
        warnings.sort_by(|(pos1, _), (pos2, _)| pos1.cmp(&pos2));
        warnings.into_iter().map(|(_, err)| err).collect()
    }

    /// Add the given warning to the program context.
    pub fn add_warn(&mut self, warn: Warning) {
        self.warnings.insert(warn.start_pos.clone(), warn);
    }

    /// Adds the given name to the set of invalid types in the program context.
    pub fn add_invalid_type(&mut self, name: &str) -> bool {
        self.stack.back_mut().unwrap().add_invalid_type(name)
    }

    /// Adds the external function signature to the context. If there was already a function with
    /// the same name, returns the old function signature.
    pub fn add_extern_fn(&mut self, sig: RichFnSig) -> Option<RichFnSig> {
        self.stack.back_mut().unwrap().add_extern_fn(sig)
    }

    /// Adds the function to the context. If there was already a function with the same name, returns
    /// the old function.
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
    pub fn add_struct(&mut self, s: RichStruct) -> Option<RichStruct> {
        self.stack.back_mut().unwrap().add_struct(s)
    }

    /// Adds the variable to the context. If there was already a variable with the same name,
    /// returns the old variable type.
    pub fn add_var(&mut self, name: &str, typ: RichType) -> Option<RichType> {
        self.stack.back_mut().unwrap().add_var(name, typ)
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
    pub fn get_struct(&self, name: &str) -> Option<&RichStruct> {
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
    pub fn get_var(&self, name: &str) -> Option<&RichType> {
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

    /// Pops the scope at the top of the stack.
    pub fn pop_scope(&mut self) {
        self.stack.pop_back();
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

    /// Returns the return type of the current scope, or none if there is no return type.
    pub fn return_type(&self) -> &Option<RichType> {
        for scope in self.stack.iter().rev() {
            if scope.kind == ScopeKind::FnBody {
                return &scope.return_type;
            }
        }

        &None
    }
}
