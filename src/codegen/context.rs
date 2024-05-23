use std::collections::HashMap;

use inkwell::basic_block::BasicBlock;
use inkwell::values::BasicValueEnum;

/// Stores information about a loop that is being compiled.
pub struct LoopContext<'ctx> {
    pub cond_block: BasicBlock<'ctx>,
    pub body_block: BasicBlock<'ctx>,
    pub update_block: Option<BasicBlock<'ctx>>,
    pub end_block: Option<BasicBlock<'ctx>>,
    pub guarantees_return: bool,
    pub guarantees_terminator: bool,
    pub contains_return: bool,
}

impl<'ctx> LoopContext<'ctx> {
    pub fn new(cond_block: BasicBlock<'ctx>, body_block: BasicBlock<'ctx>) -> Self {
        LoopContext {
            cond_block,
            body_block,
            update_block: None,
            end_block: None,
            guarantees_return: false,
            guarantees_terminator: false,
            contains_return: false,
        }
    }
}

/// Stores information about a `from` expression that is being compiled.
pub struct FromContext<'ctx> {
    pub end_block: BasicBlock<'ctx>,
    /// Maps basic block to the value that was yielded from that block.
    pub yielded_vales: HashMap<BasicBlock<'ctx>, BasicValueEnum<'ctx>>,
    pub guarantees_return: bool,
}

impl<'ctx> FromContext<'ctx> {
    pub fn new(end_block: BasicBlock<'ctx>) -> Self {
        FromContext {
            end_block,
            yielded_vales: Default::default(),
            guarantees_return: false,
        }
    }
}

/// Stores information about a function that is being compiled.
pub struct FnContext {
    pub guarantees_return: bool,
}

impl FnContext {
    pub fn new() -> Self {
        FnContext {
            guarantees_return: false,
        }
    }
}

/// Stores information about a statement that is being compiled.
pub struct StatementContext {
    pub guarantees_return: bool,
    pub guarantees_terminator: bool,
}

impl StatementContext {
    pub fn new() -> Self {
        StatementContext {
            guarantees_return: false,
            guarantees_terminator: false,
        }
    }
}

/// Stores information about a branch that is being compiled.
pub struct BranchContext {
    pub guarantees_return: bool,
    pub guarantees_terminator: bool,
}

impl BranchContext {
    pub fn new() -> Self {
        BranchContext {
            guarantees_return: false,
            guarantees_terminator: false,
        }
    }
}

/// Stores information about the current closure or statement being compiled.
pub enum CompilationContext<'ctx> {
    Loop(LoopContext<'ctx>),
    From(FromContext<'ctx>),
    Branch(BranchContext),
    Func(FnContext),
    Statement(StatementContext),
}

impl<'ctx> CompilationContext<'ctx> {
    pub fn to_loop(self) -> LoopContext<'ctx> {
        match self {
            CompilationContext::Loop(ctx) => ctx,
            _ => panic!("cannot cast context to LoopContext"),
        }
    }

    pub fn to_from(self) -> FromContext<'ctx> {
        match self {
            CompilationContext::From(ctx) => ctx,
            _ => panic!("cannot cast context to DoContext"),
        }
    }

    pub fn to_branch(self) -> BranchContext {
        match self {
            CompilationContext::Branch(ctx) => ctx,
            _ => panic!("cannot cast context to BranchContext"),
        }
    }

    pub fn to_fn(self) -> FnContext {
        match self {
            CompilationContext::Func(ctx) => ctx,
            _ => panic!("cannot cast context to FnContext"),
        }
    }

    pub fn to_statement(self) -> StatementContext {
        match self {
            CompilationContext::Statement(ctx) => ctx,
            _ => panic!("cannot cast context to StatementContext"),
        }
    }
}
