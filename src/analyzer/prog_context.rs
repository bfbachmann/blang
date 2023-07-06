use std::collections::{HashMap, VecDeque};

use crate::parser::func::Function;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::var_dec::VariableDeclaration;

enum ScopeKind {
    FnBody,
    Inline,
    Branch,
    Loop,
}

/// Represents a scope in the program. Each scope corresponds to a unique closure which can
/// be a function body, an inline closure, a branch, or a loop.
pub struct Scope {
    vars: HashMap<String, VariableDeclaration>,
    fns: HashMap<String, Function>,
    extern_fns: HashMap<String, FunctionSignature>,
    kind: ScopeKind,
}

impl Scope {
    /// Creates a new scope.
    pub fn new() -> Self {
        Scope {
            vars: HashMap::new(),
            fns: HashMap::new(),
            extern_fns: HashMap::new(),
            kind: ScopeKind::Inline,
        }
    }

    // Adds the signature of the external function to the scope. If there was already a function
    // with the same name in the scope, returns the old function. Use this method to record the
    // existence of functions before their bodies are analyzed.
    fn add_extern_fn(&mut self, sig: FunctionSignature) -> Option<FunctionSignature> {
        self.extern_fns.insert(sig.name.to_string(), sig)
    }

    // Returns the external function signature with the given name from the scope, or None if no
    // such external function exists.
    fn get_extern_fn(&self, name: &str) -> Option<&FunctionSignature> {
        self.extern_fns.get(name)
    }

    // Adds the function to the scope. If there was already a function with the same name in the
    // scope, returns the old function.
    fn add_fn(&mut self, func: Function) -> Option<Function> {
        self.fns.insert(func.signature.name.to_string(), func)
    }

    // Adds the variable to the scope. If there was already a variable with the same name in the
    // scope, returns the old variable.
    fn add_var(&mut self, var_dec: VariableDeclaration) -> Option<VariableDeclaration> {
        self.vars.insert(var_dec.name.clone(), var_dec)
    }

    // Returns the function with the given name from the scope, or None if no such function exists.
    fn get_fn(&self, name: &str) -> Option<&Function> {
        self.fns.get(name)
    }

    // Returns the variable with the given name from the scope, or None if no such variable exists.
    fn get_var(&self, name: &str) -> Option<&VariableDeclaration> {
        self.vars.get(name)
    }
}

/// Represents the current program stack and analysis state.
pub struct ProgramContext {
    stack: VecDeque<Scope>,
}

impl ProgramContext {
    /// Returns a new ProgramContext with a single initialized scope representing the global
    /// scope.
    pub fn new() -> Self {
        ProgramContext {
            stack: VecDeque::from([Scope::new()]),
        }
    }

    /// Adds the external function signature to the context. If there was already a function with
    /// the same name, returns the old function signature.
    pub fn add_extern_fn(&mut self, sig: FunctionSignature) -> Option<FunctionSignature> {
        self.stack.back_mut().unwrap().add_extern_fn(sig)
    }

    /// Adds the function to the context. If there was already a function with the same name, returns
    /// the old function.
    pub fn add_fn(&mut self, func: Function) -> Option<Function> {
        self.stack.back_mut().unwrap().add_fn(func)
    }

    /// Adds the variable to the context. If there was already a variable with the same name, returns
    /// the old variable.
    pub fn add_var(&mut self, var_dec: VariableDeclaration) -> Option<VariableDeclaration> {
        self.stack.back_mut().unwrap().add_var(var_dec)
    }

    /// Attempts to locate the external function signature with the given name and returns it,
    /// if found.
    pub fn get_extern_fn(&self, name: &str) -> Option<&FunctionSignature> {
        // Search up the stack from the current scope.
        for scope in self.stack.iter().rev() {
            if let Some(sig) = scope.get_extern_fn(name) {
                return Some(sig);
            }
        }

        None
    }

    /// Attempts to locate the function with the given name and returns it, if found.
    pub fn get_fn(&self, name: &str) -> Option<&Function> {
        // Search up the stack from the current scope.
        for scope in self.stack.iter().rev() {
            if let Some(func) = scope.get_fn(name) {
                return Some(func);
            }
        }

        None
    }

    /// Attempts to locate the variable with the given name and returns it, if found.
    pub fn get_var(&self, name: &str) -> Option<&VariableDeclaration> {
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
}
