use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::ast::closure::{analyze_break, analyze_continue, AClosure};
use crate::analyzer::ast::cond::ACond;
use crate::analyzer::ast::fn_call::AFnCall;
use crate::analyzer::ast::func::AFn;
use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::ast::r#enum::AEnumType;
use crate::analyzer::ast::r#loop::ALoop;
use crate::analyzer::ast::r#match::AMatch;
use crate::analyzer::ast::r#struct::AStructType;
use crate::analyzer::ast::r#yield::AYield;
use crate::analyzer::ast::ret::ARet;
use crate::analyzer::ast::var_assign::AVarAssign;
use crate::analyzer::ast::var_dec::AVarDecl;
use crate::analyzer::error::err_invalid_statement;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::ScopeKind;
use crate::lexer::pos::{Locatable, Span};
use crate::parser::ast::statement::Statement;

/// Represents a semantically valid and type-rich statement.
#[derive(PartialEq, Debug, Clone)]
pub enum AStatement {
    VariableDeclaration(AVarDecl),
    VariableAssignment(AVarAssign),
    FunctionDeclaration(AFn),
    Closure(AClosure),
    FunctionCall(AFnCall),
    Conditional(ACond),
    Match(AMatch),
    Loop(Box<ALoop>),
    Break(Span),
    Continue(Span),
    Return(ARet),
    Yield(AYield),
    StructTypeDeclaration(AStructType),
    EnumTypeDeclaration(AEnumType),
    /// An external function declaration.
    Const(AConst),
}

impl fmt::Display for AStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            AStatement::VariableDeclaration(v) => write!(f, "{}", v),
            AStatement::VariableAssignment(v) => write!(f, "{}", v),
            AStatement::FunctionDeclaration(v) => write!(f, "{}", v),
            AStatement::Closure(v) => write!(f, "{}", v),
            AStatement::FunctionCall(v) => write!(f, "{}", v),
            AStatement::Conditional(v) => write!(f, "{}", v),
            AStatement::Match(v) => write!(f, "{}", v),
            AStatement::Loop(v) => write!(f, "{}", v),
            AStatement::Break(_) => write!(f, "break"),
            AStatement::Continue(_) => write!(f, "continue"),
            AStatement::Return(v) => write!(f, "{}", v),
            AStatement::Yield(v) => write!(f, "{}", v),
            AStatement::StructTypeDeclaration(s) => write!(f, "{}", s),
            AStatement::EnumTypeDeclaration(e) => write!(f, "{}", e),
            AStatement::Const(const_decl) => {
                write!(f, "const {}", const_decl)
            }
        }
    }
}

impl Locatable for AStatement {
    fn span(&self) -> &Span {
        match self {
            AStatement::VariableDeclaration(var_decl) => &var_decl.val.span,
            AStatement::VariableAssignment(assign) => &assign.target.span,
            AStatement::FunctionDeclaration(func) => &func.span,
            AStatement::Closure(closure) => &closure.span,
            AStatement::FunctionCall(call) => &call.span,
            AStatement::Conditional(cond) => &cond.span,
            AStatement::Match(match_) => &match_.span,
            AStatement::Loop(loop_) => &loop_.span,
            AStatement::Break(span) => span,
            AStatement::Continue(span) => span,
            AStatement::Return(ret) => &ret.span,
            AStatement::Yield(yield_) => &yield_.span,
            AStatement::StructTypeDeclaration(decl) => &decl.span,
            AStatement::EnumTypeDeclaration(decl) => &decl.span,
            AStatement::Const(const_) => &const_.span,
        }
    }
}

impl AStatement {
    /// Performs semantic analysis on the given statement and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, statement: &Statement) -> Self {
        match statement {
            Statement::VariableDeclaration(var_decl) => {
                AStatement::VariableDeclaration(AVarDecl::from(ctx, var_decl))
            }

            Statement::VariableAssignment(var_assign) => {
                AStatement::VariableAssignment(AVarAssign::from(ctx, var_assign))
            }

            Statement::FunctionDeclaration(fn_decl) => {
                // Analyze the function and add it to the program context so we can reference it
                // later.
                let a_fn = AFn::from(ctx, fn_decl);
                ctx.insert_analyzed_fn(a_fn.clone());
                AStatement::FunctionDeclaration(a_fn)
            }

            Statement::Closure(closure) => AStatement::Closure(AClosure::from(
                ctx,
                closure,
                ScopeKind::InlineClosure,
                vec![],
                None,
            )),

            Statement::FunctionCall(call) => {
                AStatement::FunctionCall(AFnCall::from(ctx, call, None))
            }

            Statement::Conditional(cond) => AStatement::Conditional(ACond::from(ctx, cond)),

            Statement::Match(match_) => AStatement::Match(AMatch::from(ctx, match_)),

            Statement::Loop(loop_) => AStatement::Loop(Box::new(ALoop::from(ctx, &loop_))),

            Statement::Break(br) => {
                analyze_break(ctx, &br);
                AStatement::Break(br.span)
            }

            Statement::Continue(cont) => {
                analyze_continue(ctx, &cont);
                AStatement::Continue(cont.span)
            }

            Statement::Return(ret) => {
                let a_ret = ARet::from(ctx, ret);
                AStatement::Return(a_ret)
            }

            Statement::Yield(yld) => AStatement::Yield(AYield::from(ctx, yld)),

            Statement::StructDeclaration(s) => {
                AStatement::StructTypeDeclaration(AStructType::from(ctx, &s))
            }

            Statement::EnumDeclaration(e) => {
                AStatement::EnumTypeDeclaration(AEnumType::from(ctx, &e))
            }

            Statement::ConstDeclaration(const_decl) => {
                AStatement::Const(AConst::from(ctx, const_decl))
            }

            Statement::Use(_) | Statement::Impl(_) | Statement::ExternFn(_) => {
                ctx.insert_err(err_invalid_statement(*statement.span()));
                AStatement::Closure(AClosure::new_empty())
            }

            Statement::SpecDeclaration(_) => {
                // This should never happen as specs should be skipped – they're analyzed before
                // we start analyzing other program statements.
                unreachable!()
            }
        }
    }
}
