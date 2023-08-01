use crate::analyzer::r#struct::RichStruct;
use crate::parser::arg::Argument;
use crate::parser::expr::Expression;
use std::collections::hash_map::Iter;
use std::collections::{HashMap, VecDeque};
use std::fmt;

use crate::parser::func::Function;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::r#struct::Struct;
use crate::parser::r#type::Type;
use crate::parser::var_dec::VariableDeclaration;

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
    // TODO: VariableDeclaration contains potentially unnecessary expression.
    vars: HashMap<String, VariableDeclaration>,
    extern_fns: HashMap<String, FunctionSignature>,
    fns: HashMap<String, Function>,
    extern_structs: HashMap<String, Struct>,
    structs: HashMap<String, RichStruct>,
    kind: ScopeKind,
    return_type: Option<Type>,
}

impl Scope {
    /// Creates a new scope.
    pub fn new(kind: ScopeKind, args: Vec<Argument>, return_type: Option<Type>) -> Self {
        let mut vars = HashMap::new();

        // If there are args, add them to the current scope variables.
        for arg in args {
            // TODO: don't use placeholder expression here.
            vars.insert(
                arg.name.clone(),
                VariableDeclaration::new(arg.typ, arg.name.clone(), Expression::BoolLiteral(false)),
            );
        }

        Scope {
            vars,
            extern_fns: HashMap::new(),
            fns: HashMap::new(),
            extern_structs: HashMap::new(),
            structs: HashMap::new(),
            kind,
            return_type,
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

    // Adds the external struct type to the scope. If there was already a struct type with the same
    // name in the scope, returns the old type.
    fn add_extern_struct(&mut self, s: Struct) -> Option<Struct> {
        self.extern_structs.insert(s.name.to_string(), s)
    }

    // Adds the struct type to the scope. If there was already a struct type with the same name in
    // the scope, returns the old type.
    fn add_struct(&mut self, s: RichStruct) -> Option<RichStruct> {
        self.structs.insert(s.name.to_string(), s)
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

    // Returns the extern struct type with the given name from the scope, or None if no such type
    // exists.
    fn get_extern_struct(&self, name: &str) -> Option<&Struct> {
        self.extern_structs.get(name)
    }

    /// Returns an iterator over all extern structs in this scope.
    fn extern_structs(&self) -> Iter<String, Struct> {
        self.extern_structs.iter()
    }

    // Returns the struct type with the given name from the scope, or None if no such type exists.
    fn get_struct(&self, name: &str) -> Option<&RichStruct> {
        self.structs.get(name)
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
            stack: VecDeque::from([Scope::new(ScopeKind::Inline, vec![], None)]),
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

    /// Adds the external struct type to the context. If there was already a struct type with the
    /// same name, returns the old type.
    pub fn add_extern_struct(&mut self, s: Struct) -> Option<Struct> {
        self.stack.back_mut().unwrap().add_extern_struct(s)
    }

    /// Adds the struct type to the context. If there was already a struct type with the same name,
    /// returns the old type.
    pub fn add_struct(&mut self, s: RichStruct) -> Option<RichStruct> {
        self.stack.back_mut().unwrap().add_struct(s)
    }

    /// Adds the variable to the context. If there was already a variable with the same name,
    /// returns the old variable.
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

    /// Attempts to locate the extern struct type with the given name and returns it, if found.
    pub fn get_extern_struct(&self, name: &str) -> Option<&Struct> {
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
    pub fn extern_structs(&self) -> Vec<&Struct> {
        let mut extern_structs = vec![];
        for scope in self.stack.iter() {
            for (_, struct_type) in scope.extern_structs() {
                extern_structs.push(struct_type);
            }
        }

        extern_structs
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
    pub fn return_type(&self) -> &Option<Type> {
        for scope in self.stack.iter().rev() {
            if scope.kind == ScopeKind::FnBody {
                return &scope.return_type;
            }
        }

        &None
    }
}
