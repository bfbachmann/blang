use inkwell::basic_block::BasicBlock;

pub struct LoopContext<'ctx> {
    pub begin_block: BasicBlock<'ctx>,
    pub end_block: Option<BasicBlock<'ctx>>,
    pub guarantees_return: bool,
    pub guarantees_terminator: bool,
    pub contains_return: bool,
}

impl<'ctx> LoopContext<'ctx> {
    pub fn new(begin_block: BasicBlock<'ctx>) -> Self {
        LoopContext {
            begin_block,
            end_block: None,
            guarantees_return: false,
            guarantees_terminator: false,
            contains_return: false,
        }
    }
}

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
