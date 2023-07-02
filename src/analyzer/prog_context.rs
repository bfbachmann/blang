use crate::parser::expr::Expression;
use crate::parser::r#fn::Function;
use crate::parser::r#type::Type;
use crate::parser::var_dec::VariableDeclaration;
use std::collections::{HashMap, VecDeque};
use std::env::var;

/// Represents a stack frame in the program. Each frame corresponds to a unique closure which can
/// be a function body, an inline closure, or a branch.
pub struct Frame {
    local_vars: HashMap<String, Type>,
    local_fns: HashMap<String, Function>,
}

impl Frame {
    pub fn new() -> Self {
        Frame {
            local_vars: HashMap::new(),
            local_fns: HashMap::new(),
        }
    }
}

/// Represents the current program stack and analysis state.
pub struct ProgramContext {
    stack: VecDeque<Frame>,
}

impl ProgramContext {
    /// Returns a new ProgramContext with a single initialized stack frame.
    pub fn new() -> Self {
        ProgramContext {
            stack: VecDeque::from([Frame::new()]),
        }
    }

    /// Attempts to find the type of the variable with the given name by searching for the variable
    /// in each frame of the stack. The stack is searched from the bottom up, thereby giving greater
    /// precedence to variables defined in scopes closer to the point of reference.
    pub fn resolve_var_type(&self, var_ref: Expression::VariableReference) -> Option<&Type> {
        for frame in self.stack.iter().rev() {
            if let Some(typ) = frame.local_vars.get(var_ref.1.as_str()) {
                return Some(typ);
            }
        }

        None
    }

    /// Returns true if a variable exists with the given name in the current scope.
    pub fn var_is_defined_locally(&self, var_name: &str) -> bool {
        self.stack.back().unwrap().local_vars.contains_key(var_name)
    }

    /// Records the given variable name and its type to the current stack frame.
    pub fn add_local_var(&mut self, var: VariableDeclaration) {
        let cur_frame = self.stack.back_mut().unwrap();
        cur_frame.local_vars.insert(var.name, var.typ);
    }

    /// Records the given function to the current stack frame.
    pub fn add_local_fn(&mut self, func: Function) {
        let cur_frame = self.stack.back_mut().unwrap();
        cur_frame
            .local_fns
            .insert(func.signature.name.clone(), func);
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
