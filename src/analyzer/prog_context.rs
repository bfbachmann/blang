use std::collections::{HashMap, VecDeque};
use std::env::var;

use crate::parser::expr::Expression;
use crate::parser::r#fn::Function;
use crate::parser::r#type::Type;
use crate::parser::var_dec::VariableDeclaration;

/// Represents a stack frame in the program. Each frame corresponds to a unique closure which can
/// be a function body, an inline closure, or a branch.
pub struct Frame {
    vars: HashMap<String, VariableDeclaration>,
    fns: HashMap<String, Function>,
    is_fn_body: bool,
}

impl Frame {
    /// Creates a new frame. `is_fn_body` should be true if the frame represents a function body,
    /// and false otherwise (i.e. if it's an inline, branch, or loop closure).
    pub fn new(is_fn_body: bool) -> Self {
        Frame {
            vars: HashMap::new(),
            fns: HashMap::new(),
            is_fn_body,
        }
    }

    // Adds the function to the frame. If there was already a function with the same name in the
    // frame, returns the old function.
    fn add_fn(&mut self, func: Function) -> Option<Function> {
        self.fns.insert(func.signature.name.to_string(), func)
    }

    // Adds the variable to the frame. If there was already a variable with the same name in the
    // frame, returns the old variable.
    fn add_var(&mut self, var_dec: VariableDeclaration) -> Option<VariableDeclaration> {
        self.vars.insert(var_dec.name.clone(), var_dec)
    }

    // Returns the function with the given name from the frame, or None if no such function exists.
    fn get_fn(&self, name: &str) -> Option<&Function> {
        self.fns.get(name)
    }

    // Returns the variable with the given name from the frame, or None if no such variable exists.
    fn get_var(&self, name: &str) -> Option<&VariableDeclaration> {
        self.vars.get(name)
    }
}

/// Represents the current program stack and analysis state.
pub struct ProgramContext {
    stack: VecDeque<Frame>,
}

impl ProgramContext {
    /// Returns a new ProgramContext with a single initialized stack frame representing the global
    /// scope.
    pub fn new() -> Self {
        ProgramContext {
            stack: VecDeque::from([Frame::new(false)]),
        }
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

    /// Attempts to locate the function with the given name and returns it, if found.
    pub fn get_fn(&self, name: &str) -> Option<&Function> {
        // Try to find the function in the global frame.
        if let Some(func) = self.stack.front().unwrap().get_fn(name) {
            return Some(func);
        }

        // We can keep searching up the stack as long as we remain within frames that are not
        // function bodies (i.e. we're in some inline, branch, or loop closures). In other words,
        // we can't step outside of a function body to look for the function.
        for frame in self.stack.iter().rev() {
            if let Some(func) = frame.get_fn(name) {
                return Some(func);
            }

            if frame.is_fn_body {
                break;
            }
        }

        None
    }

    /// Attempts to locate the variable with the given name and returns it, if found.
    pub fn get_var(&self, name: &str) -> Option<&VariableDeclaration> {
        // Try to find the function in the global frame.
        if let Some(var) = self.stack.front().unwrap().get_var(name) {
            return Some(var);
        }

        // We can keep searching up the stack as long as we remain within frames that are not
        // function bodies (i.e. we're in some inline, branch, or loop closures). In other words,
        // we can't step outside of a function body to look for the function.
        for frame in self.stack.iter().rev() {
            if let Some(var) = frame.get_var(name) {
                return Some(var);
            }

            if frame.is_fn_body {
                break;
            }
        }

        None
    }

    /// Adds the given frame to the top of the stack.
    pub fn push_frame(&mut self, frame: Frame) {
        self.stack.push_back(frame);
    }

    /// Pops the frame at the top of the stack.
    pub fn pop_frame(&mut self) {
        self.stack.pop_back();
    }
}
