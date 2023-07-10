use core::fmt;
use std::fmt::Formatter;

use crate::analyzer::closure::{analyze_break, RichClosure};
use crate::analyzer::cond::RichCond;
use crate::analyzer::func::{RichFn, RichFnCall, RichRet};
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::var_assign::RichVarAssign;
use crate::analyzer::var_dec::RichVarDecl;
use crate::analyzer::AnalyzeResult;
use crate::parser::statement::Statement;

#[derive(PartialEq, Debug)]
pub enum RichStatement {
    VariableDeclaration(RichVarDecl),
    VariableAssignment(RichVarAssign),
    FunctionDeclaration(RichFn),
    Closure(RichClosure),
    FunctionCall(RichFnCall),
    Conditional(RichCond),
    Loop(RichClosure),
    Break,
    Return(RichRet),
}

impl fmt::Display for RichStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            RichStatement::VariableDeclaration(v) => write!(f, "{}", v),
            RichStatement::VariableAssignment(v) => write!(f, "{}", v),
            RichStatement::FunctionDeclaration(v) => write!(f, "{}", v),
            RichStatement::Closure(v) => write!(f, "{}", v),
            RichStatement::FunctionCall(v) => write!(f, "{}", v),
            RichStatement::Conditional(v) => write!(f, "{}", v),
            RichStatement::Loop(v) => write!(f, "{}", v),
            RichStatement::Break => write!(f, "break"),
            RichStatement::Return(v) => write!(f, "{}", v),
        }
    }
}

impl RichStatement {
    pub fn from(ctx: &mut ProgramContext, statement: Statement) -> AnalyzeResult<Self> {
        match statement {
            Statement::VariableDeclaration(var_decl) => match RichVarDecl::from(ctx, var_decl) {
                Ok(rvd) => Ok(RichStatement::VariableDeclaration(rvd)),
                Err(e) => Err(e),
            },
            Statement::VariableAssignment(var_assign) => match RichVarAssign::from(ctx, var_assign)
            {
                Ok(va) => Ok(RichStatement::VariableAssignment(va)),
                Err(e) => Err(e),
            },
            Statement::FunctionDeclaration(fn_decl) => match RichFn::from(ctx, fn_decl) {
                Ok(fd) => Ok(RichStatement::FunctionDeclaration(fd)),
                Err(e) => Err(e),
            },
            Statement::Closure(closure) => {
                match RichClosure::from(ctx, closure, ScopeKind::Inline, vec![], None) {
                    Ok(rc) => Ok(RichStatement::Closure(rc)),
                    Err(e) => Err(e),
                }
            }
            Statement::FunctionCall(call) => match RichFnCall::from(ctx, call) {
                Ok(rfc) => Ok(RichStatement::FunctionCall(rfc)),
                Err(e) => Err(e),
            },
            Statement::Conditional(cond) => match RichCond::from(ctx, cond) {
                Ok(rc) => Ok(RichStatement::Conditional(rc)),
                Err(e) => Err(e),
            },
            Statement::Loop(loop_) => {
                match RichClosure::from(ctx, loop_.closure, ScopeKind::Loop, vec![], None) {
                    Ok(rc) => Ok(RichStatement::Loop(rc)),
                    Err(e) => Err(e),
                }
            }
            Statement::Break => match analyze_break(ctx) {
                Ok(_) => Ok(RichStatement::Break),
                Err(e) => Err(e),
            },
            Statement::Return(expr) => match RichRet::from(ctx, expr) {
                Ok(rr) => Ok(RichStatement::Return(rr)),
                Err(e) => Err(e),
            },
        }
    }
}
