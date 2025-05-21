use std::collections::HashMap;

use crate::analyzer::ast::r#const::AConst;
use inkwell::basic_block::BasicBlock;
use inkwell::values::{BasicValueEnum, PointerValue};

/// Stores information about a loop that is being compiled.
pub struct LoopScope<'ctx> {
    pub cond_block: BasicBlock<'ctx>,
    pub body_block: BasicBlock<'ctx>,
    pub update_block: Option<BasicBlock<'ctx>>,
    pub end_block: Option<BasicBlock<'ctx>>,
    pub guarantees_return: bool,
    pub guarantees_terminator: bool,
    pub contains_return: bool,
}

impl<'ctx> LoopScope<'ctx> {
    pub fn new(cond_block: BasicBlock<'ctx>, body_block: BasicBlock<'ctx>) -> Self {
        LoopScope {
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
pub struct FromScope<'ctx> {
    pub end_block: BasicBlock<'ctx>,
    /// Maps basic block to the value that was yielded from that block.
    pub yielded_vales: HashMap<BasicBlock<'ctx>, BasicValueEnum<'ctx>>,
    pub guarantees_return: bool,
}

impl<'ctx> FromScope<'ctx> {
    pub fn new(end_block: BasicBlock<'ctx>) -> Self {
        FromScope {
            end_block,
            yielded_vales: Default::default(),
            guarantees_return: false,
        }
    }
}

/// Stores information about a function that is being compiled.
pub struct FnScope {
    pub guarantees_return: bool,
}

impl FnScope {
    pub fn new() -> Self {
        FnScope {
            guarantees_return: false,
        }
    }
}

#[derive(Default)]
pub struct BasicScope {
    pub guarantees_return: bool,
    pub guarantees_terminator: bool,
}

/// Stores information about the current closure or statement scope.
pub struct CodegenScope<'ctx> {
    pub kind: CodegenScopeKind<'ctx>,
    pub consts: HashMap<String, AConst>,
    pub ll_vars: HashMap<String, PointerValue<'ctx>>,
}

impl<'ctx> CodegenScope<'ctx> {
    pub fn new_fn() -> CodegenScope<'ctx> {
        CodegenScope {
            kind: CodegenScopeKind::Func(FnScope::new()),
            consts: Default::default(),
            ll_vars: Default::default(),
        }
    }

    pub fn new_closure() -> CodegenScope<'ctx> {
        CodegenScope {
            kind: CodegenScopeKind::Closure(BasicScope::default()),
            consts: Default::default(),
            ll_vars: Default::default(),
        }
    }

    pub fn new_statement() -> CodegenScope<'ctx> {
        CodegenScope {
            kind: CodegenScopeKind::Statement(BasicScope::default()),
            consts: Default::default(),
            ll_vars: Default::default(),
        }
    }

    pub fn new_branch() -> CodegenScope<'ctx> {
        CodegenScope {
            kind: CodegenScopeKind::Branch(BasicScope::default()),
            consts: Default::default(),
            ll_vars: Default::default(),
        }
    }

    pub fn new_loop(
        cond_block: BasicBlock<'ctx>,
        body_block: BasicBlock<'ctx>,
    ) -> CodegenScope<'ctx> {
        CodegenScope {
            kind: CodegenScopeKind::Loop(LoopScope::new(cond_block, body_block)),
            consts: Default::default(),
            ll_vars: Default::default(),
        }
    }

    pub fn new_from(end_block: BasicBlock<'ctx>) -> CodegenScope<'ctx> {
        CodegenScope {
            kind: CodegenScopeKind::From(FromScope::new(end_block)),
            consts: Default::default(),
            ll_vars: Default::default(),
        }
    }
}

pub enum CodegenScopeKind<'ctx> {
    Loop(LoopScope<'ctx>),
    From(FromScope<'ctx>),
    Branch(BasicScope),
    Func(FnScope),
    Statement(BasicScope),
    Closure(BasicScope),
}

impl<'ctx> CodegenScopeKind<'ctx> {
    pub fn into_loop(self) -> LoopScope<'ctx> {
        match self {
            CodegenScopeKind::Loop(scope) => scope,
            _ => panic!("cannot cast scope to Loop"),
        }
    }

    pub fn into_from(self) -> FromScope<'ctx> {
        match self {
            CodegenScopeKind::From(scope) => scope,
            _ => panic!("cannot cast scope to From"),
        }
    }

    pub fn into_branch(self) -> BasicScope {
        match self {
            CodegenScopeKind::Branch(scope) => scope,
            _ => panic!("cannot cast scope to Branch"),
        }
    }

    pub fn into_fn(self) -> FnScope {
        match self {
            CodegenScopeKind::Func(scope) => scope,
            _ => panic!("cannot cast scope to Func"),
        }
    }

    pub fn into_statement(self) -> BasicScope {
        match self {
            CodegenScopeKind::Statement(scope) => scope,
            _ => panic!("cannot cast scope to Statement"),
        }
    }
}
