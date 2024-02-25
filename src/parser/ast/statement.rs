use std::fmt;

use colored::Colorize;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::closure::Closure;
use crate::parser::ast::cond::Conditional;
use crate::parser::ast::cont::Continue;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::ext::Extern;
use crate::parser::ast::func::Function;
use crate::parser::ast::func_call::FuncCall;
use crate::parser::ast::r#break::Break;
use crate::parser::ast::r#const::ConstBlock;
use crate::parser::ast::r#enum::EnumType;
use crate::parser::ast::r#impl::Impl;
use crate::parser::ast::r#loop::Loop;
use crate::parser::ast::r#struct::StructType;
use crate::parser::ast::r#use::UsedModule;
use crate::parser::ast::ret::Ret;
use crate::parser::ast::spec::Spec;
use crate::parser::ast::var_assign::VariableAssignment;
use crate::parser::ast::var_dec::VariableDeclaration;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::source::Source;

/// Represents a statement.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Statement {
    VariableDeclaration(VariableDeclaration),
    VariableAssignment(VariableAssignment),
    FunctionDeclaration(Function),
    Closure(Closure),
    FunctionCall(FuncCall),
    Conditional(Conditional),
    Loop(Box<Loop>),
    Break(Break),
    Continue(Continue),
    Return(Ret),
    StructDeclaration(StructType),
    EnumDeclaration(EnumType),
    ExternFns(Extern),
    Consts(ConstBlock),
    Impl(Impl),
    SpecDeclaration(Spec),
    Use(UsedModule),
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Statement::VariableDeclaration(var_dec) => {
                if let Some(typ) = &var_dec.maybe_type {
                    write!(f, "let {}: {} = ...", var_dec.name, typ)
                } else {
                    write!(f, "let {} = ...", var_dec.name)
                }
            }
            Statement::VariableAssignment(var_assign) => {
                write!(f, "{} = ...", var_assign.target)
            }
            Statement::FunctionDeclaration(func) => {
                write!(f, "{}", func.signature)
            }
            Statement::Closure(_) => {
                write!(f, "{{ ... }}")
            }
            Statement::FunctionCall(call) => {
                write!(f, "{}(...)", call.fn_expr)
            }
            Statement::Conditional(_) => {
                write!(f, "if ...")
            }
            Statement::Loop(_) => {
                write!(f, "loop {{ ... }}")
            }
            Statement::Break(_) => {
                write!(f, "break")
            }
            Statement::Continue(_) => {
                write!(f, "continue")
            }
            Statement::Return(ret) => {
                if let Some(val) = &ret.value {
                    write!(f, "return {}", val)
                } else {
                    write!(f, "return")
                }
            }
            Statement::StructDeclaration(s) => {
                write!(f, "{}", s)
            }
            Statement::EnumDeclaration(e) => {
                write!(f, "{}", e)
            }
            Statement::ExternFns(extern_fn) => {
                write!(f, "{}", extern_fn)
            }
            Statement::Consts(const_block) => {
                write!(f, "{}", const_block)
            }
            Statement::Use(used_mod) => {
                write!(f, "{}", used_mod)
            }
            Statement::Impl(impl_) => {
                write!(
                    f,
                    "impl {} {{ <{} member functions> }}",
                    impl_.typ,
                    impl_.member_fns.len(),
                )
            }
            Statement::SpecDeclaration(spec_) => {
                write!(
                    f,
                    "spec {} {{ <{} functions> }}",
                    spec_.name,
                    spec_.fn_sigs.len()
                )
            }
        }
    }
}

impl Locatable for Statement {
    fn start_pos(&self) -> &Position {
        match self {
            Statement::VariableDeclaration(var_dec) => var_dec.start_pos(),
            Statement::VariableAssignment(var_assign) => var_assign.start_pos(),
            Statement::FunctionDeclaration(func) => func.start_pos(),
            Statement::Closure(closure) => closure.start_pos(),
            Statement::FunctionCall(call) => call.start_pos(),
            Statement::Conditional(cond) => cond.start_pos(),
            Statement::Loop(l) => l.start_pos(),
            Statement::Break(br) => br.start_pos(),
            Statement::Continue(cont) => cont.start_pos(),
            Statement::Return(ret) => ret.start_pos(),
            Statement::StructDeclaration(s) => s.start_pos(),
            Statement::EnumDeclaration(e) => e.start_pos(),
            Statement::ExternFns(e) => e.start_pos(),
            Statement::Consts(c) => c.start_pos(),
            Statement::Use(u) => u.start_pos(),
            Statement::Impl(i) => i.start_pos(),
            Statement::SpecDeclaration(t) => t.start_pos(),
        }
    }

    fn end_pos(&self) -> &Position {
        match self {
            Statement::VariableDeclaration(var_dec) => var_dec.end_pos(),
            Statement::VariableAssignment(var_assign) => var_assign.end_pos(),
            Statement::FunctionDeclaration(func) => func.end_pos(),
            Statement::Closure(closure) => closure.end_pos(),
            Statement::FunctionCall(call) => call.end_pos(),
            Statement::Conditional(cond) => cond.end_pos(),
            Statement::Loop(l) => l.end_pos(),
            Statement::Break(br) => br.end_pos(),
            Statement::Continue(cont) => cont.end_pos(),
            Statement::Return(ret) => ret.end_pos(),
            Statement::StructDeclaration(s) => s.end_pos(),
            Statement::EnumDeclaration(e) => e.end_pos(),
            Statement::ExternFns(e) => e.end_pos(),
            Statement::Consts(c) => c.end_pos(),
            Statement::Use(u) => u.end_pos(),
            Statement::Impl(i) => i.end_pos(),
            Statement::SpecDeclaration(t) => t.end_pos(),
        }
    }
}

impl Statement {
    /// Parses a statement. Statements can be any of the following:
    ///  - variable declaration (see `VariableDeclaration::from`)
    ///  - variable assignment (see `VariableAssignment::from`)
    ///  - function declaration (see `Function::from`)
    ///  - closure (see `Closure::from`)
    ///  - expression (see `Expression::from`)
    ///  - conditional (see `Conditional::from`)
    ///  - loop (see `Loop::from`)
    ///  - break
    ///  - continue
    ///  - return (of the form `return <expr>` where `expr` is an expression)
    ///  - struct declaration (see `Struct::from`)
    ///  - extern function declaration (see `FunctionSignature::from_extern`)
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Try to use the first two tokens to figure out what type of statement will follow.
        // This works because no valid statement can contain fewer than two tokens.
        let (first, second) = (tokens.peek_next(), tokens.peek_ahead(1));
        match (&first, &second) {
            (None, None) => {
                return Err(ParseError::new(
                    ErrorKind::UnexpectedEOF,
                    "expected statement, but found EOF",
                    None,
                    Position::default(),
                    Position::default(),
                ))
            }
            (None, Some(&ref token)) | (Some(&ref token), None) => {
                return Err(ParseError::new(
                    ErrorKind::ExpectedStatement,
                    format_code!("expected statement, but found {}", token).as_str(),
                    Some(token.clone()),
                    token.start.clone(),
                    token.end.clone(),
                ))
            }
            _ => {}
        }

        match (&first.unwrap().kind, &second.unwrap().kind) {
            // If the first two tokens are "let <name>" or "let mut", it must be a variable
            // declaration.
            (TokenKind::Let, TokenKind::Identifier(_) | TokenKind::Mut) => {
                let var_decl = VariableDeclaration::from(tokens)?;
                Ok(Statement::VariableDeclaration(var_decl))
            }

            // If the first two tokens are "<identifier> =", it must be a variable assignment.
            (TokenKind::Identifier(_), TokenKind::Equal) => {
                let assign = VariableAssignment::from(tokens)?;
                Ok(Statement::VariableAssignment(assign))
            }

            // If the first token is `extern`, it's a set of external function declarations.
            (TokenKind::Extern, _) => {
                let ext = Extern::from(tokens)?;
                Ok(Statement::ExternFns(ext))
            }

            // If the first token is `const`, it's a set of constant declarations.
            (TokenKind::Const, _) => {
                let const_block = ConstBlock::from(tokens)?;
                Ok(Statement::Consts(const_block))
            }

            // If the first token is `fn`, it must be a function declaration.
            (TokenKind::Fn, _) => {
                let fn_decl = Function::from(tokens)?;
                Ok(Statement::FunctionDeclaration(fn_decl))
            }

            // If the first token is `{`, it must be a closure.
            (TokenKind::LeftBrace, _) => {
                let closure = Closure::from(tokens)?;
                Ok(Statement::Closure(closure))
            }

            // If the first token is `if`, it must be a conditional.
            (TokenKind::If, _) => {
                let cond = Conditional::from(tokens)?;
                Ok(Statement::Conditional(cond))
            }

            // If the first token is `for`, `while` or `loop`, it must be a loop.
            (TokenKind::For | TokenKind::While | TokenKind::Loop, _) => {
                let cond = Loop::from(tokens)?;
                Ok(Statement::Loop(Box::new(cond)))
            }

            // If the first token is `break`, it must be a break statement.
            (TokenKind::Break, _) => {
                let br = Break::from(tokens)?;
                Ok(Statement::Break(br))
            }

            // If the first token is `continue`, it must be a loop continue.
            (TokenKind::Continue, _) => {
                let cont = Continue::from(tokens)?;
                Ok(Statement::Continue(cont))
            }

            // If the first token is `impl`, it's the implementation of member functions for a type.
            (TokenKind::Impl, _) => {
                let impl_ = Impl::from(tokens)?;
                Ok(Statement::Impl(impl_))
            }

            // If the first token is `spec`, it's a spec declaration.
            (TokenKind::Spec, _) => {
                let spec_ = Spec::from(tokens)?;
                Ok(Statement::SpecDeclaration(spec_))
            }

            // If the first token is `return`, it must be a return statement.
            (TokenKind::Return, _) => {
                let ret_token = tokens.next().unwrap();
                let ret_token_start = ret_token.start.clone();
                let ret_token_end = ret_token.end.clone();

                // If the next token is `}` or is on the following line, it's an empty return.
                // Otherwise, we expect an expression.
                let no_ret_val = match tokens.peek_next() {
                    Some(Token {
                        kind: TokenKind::RightBrace,
                        ..
                    }) => true,

                    Some(Token { end, .. }) if end.line > ret_token_end.line => true,

                    _ => false,
                };

                if no_ret_val {
                    return Ok(Statement::Return(Ret::new(
                        None,
                        ret_token_start,
                        ret_token_end,
                    )));
                }

                let expr = Expression::from(tokens)?;
                Ok(Statement::Return(Ret::new(
                    Some(expr.clone()),
                    ret_token_start,
                    *expr.end_pos(),
                )))
            }

            // If the first token is `struct`, it must be a struct declaration.
            (TokenKind::Struct, _) => {
                let struct_decl = StructType::from(tokens)?;
                Ok(Statement::StructDeclaration(struct_decl))
            }

            // If the first token is `enum`, it must be a struct declaration.
            (TokenKind::Enum, _) => {
                let enum_decl = EnumType::from(tokens)?;
                Ok(Statement::EnumDeclaration(enum_decl))
            }

            // If the first token is `use`, it's a use (import).
            (TokenKind::Use, _) => {
                let use_mod = UsedModule::from(tokens)?;
                Ok(Statement::Use(use_mod))
            }

            // At this point the statement should be an assignment or a function call.
            (_, _) => {
                // Parse the expression.
                let start_pos = Source::current_position(tokens);
                let expr = Expression::from(tokens)?;

                // If the next token is `=`, then this is an assignment.
                if Source::parse_optional(tokens, TokenKind::Equal).is_some() {
                    // Parse the expression being assigned to the member and return the variable
                    // assignment.
                    let value = Expression::from(tokens)?;
                    let start_pos = expr.start_pos().clone();
                    return Ok(Statement::VariableAssignment(VariableAssignment::new(
                        expr, value, start_pos,
                    )));
                }

                // It's not an assignment, so it should be a function call.
                match expr {
                    Expression::FunctionCall(call) => Ok(Statement::FunctionCall(*call)),
                    _ => Err(ParseError::new(
                        ErrorKind::ExpectedStatement,
                        "expected statement, but found expression",
                        None,
                        start_pos,
                        Source::prev_position(tokens),
                    )),
                }
            }
        }
    }
}
