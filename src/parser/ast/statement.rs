use std::fmt;

use crate::lexer::pos::{Locatable, Span};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::closure::Closure;
use crate::parser::ast::cond::Conditional;
use crate::parser::ast::cont::Continue;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::func::Function;
use crate::parser::ast::func_call::FnCall;
use crate::parser::ast::r#break::Break;
use crate::parser::ast::r#const::Const;
use crate::parser::ast::r#enum::EnumType;
use crate::parser::ast::r#extern::ExternFn;
use crate::parser::ast::r#impl::Impl;
use crate::parser::ast::r#loop::Loop;
use crate::parser::ast::r#match::Match;
use crate::parser::ast::r#static::Static;
use crate::parser::ast::r#struct::StructType;
use crate::parser::ast::r#use::UsedMod;
use crate::parser::ast::r#yield::Yield;
use crate::parser::ast::ret::Ret;
use crate::parser::ast::spec::SpecType;
use crate::parser::ast::var_assign::VariableAssignment;
use crate::parser::ast::var_dec::VariableDeclaration;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::file_parser::FileParser;

/// Represents a statement.
#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    VariableDeclaration(VariableDeclaration),
    VariableAssignment(VariableAssignment),
    FunctionDeclaration(Function),
    Closure(Closure),
    FunctionCall(FnCall),
    Conditional(Conditional),
    Match(Match),
    Loop(Box<Loop>),
    Break(Break),
    Continue(Continue),
    Return(Ret),
    Yield(Yield),
    StructDeclaration(StructType),
    EnumDeclaration(EnumType),
    ExternFn(ExternFn),
    ConstDeclaration(Const),
    StaticDeclaration(Static),
    Impl(Impl),
    SpecDeclaration(SpecType),
    Use(UsedMod),
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
            Statement::Match(_) => {
                write!(f, "match ...")
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
            Statement::Yield(yld) => {
                write!(f, "yield {}", yld.value)
            }
            Statement::StructDeclaration(s) => {
                write!(f, "{}", s)
            }
            Statement::EnumDeclaration(e) => {
                write!(f, "{}", e)
            }
            Statement::ExternFn(extern_fn) => {
                write!(f, "{}", extern_fn)
            }
            Statement::ConstDeclaration(const_decl) => {
                write!(f, "{}", const_decl)
            }
            Statement::StaticDeclaration(static_decl) => {
                write!(f, "{}", static_decl)
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
    fn span(&self) -> &Span {
        match self {
            Statement::VariableDeclaration(var_dec) => var_dec.span(),
            Statement::VariableAssignment(var_assign) => var_assign.span(),
            Statement::FunctionDeclaration(func) => func.span(),
            Statement::Closure(closure) => closure.span(),
            Statement::FunctionCall(call) => call.span(),
            Statement::Conditional(cond) => cond.span(),
            Statement::Match(match_) => match_.span(),
            Statement::Loop(l) => l.span(),
            Statement::Break(br) => br.span(),
            Statement::Continue(cont) => cont.span(),
            Statement::Return(ret) => ret.span(),
            Statement::Yield(yld) => yld.span(),
            Statement::StructDeclaration(s) => s.span(),
            Statement::EnumDeclaration(e) => e.span(),
            Statement::ExternFn(e) => e.span(),
            Statement::ConstDeclaration(c) => c.span(),
            Statement::StaticDeclaration(s) => s.span(),
            Statement::Use(u) => u.span(),
            Statement::Impl(i) => i.span(),
            Statement::SpecDeclaration(t) => t.span(),
        }
    }
}

impl Statement {
    /// Parses a statement. Statements can be any of the following:
    ///  - module declaration
    ///  - variable declaration
    ///  - variable assignment
    ///  - function declaration
    ///  - closure
    ///  - expression
    ///  - conditional
    ///  - match
    ///  - loop
    ///  - break
    ///  - continue
    ///  - return (of the form `return <expr>` where `expr` is an expression)
    ///  - struct declaration
    ///  - extern function declaration
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        // Try to use the first two tokens to figure out what type of statement will follow.
        // This works because no valid statement can contain fewer than two tokens.
        let (first, second) = (parser.tokens.peek_next(), parser.tokens.peek_ahead(1));
        match (&first, &second) {
            (None, None) => {
                return Err(ParseError::new(
                    ErrorKind::UnexpectedEOF,
                    "expected statement, but found EOF",
                    None,
                    Default::default(),
                ))
            }
            (None, Some(&ref token)) | (Some(&ref token), None) => {
                return Err(ParseError::new(
                    ErrorKind::ExpectedStatement,
                    format_code!("expected statement, but found {}", token).as_str(),
                    Some(token.clone()),
                    token.span,
                ))
            }
            _ => {}
        }

        match (&first.unwrap().kind, &second.unwrap().kind) {
            // If the first two tokens are "let <name>" or "let mut", it must be a variable
            // declaration.
            (TokenKind::Let, TokenKind::Identifier(_) | TokenKind::Mut) => {
                let var_decl = VariableDeclaration::parse(parser)?;
                Ok(Statement::VariableDeclaration(var_decl))
            }

            // If the next tokens are `extern` or `pub extern`, it's an
            // external function declaration.
            (TokenKind::Extern, _) | (TokenKind::Pub, TokenKind::Extern) => {
                let ext = ExternFn::parse(parser)?;
                Ok(Statement::ExternFn(ext))
            }

            // If the nex tokens are `const` or `pub const`, it's a constant declaration.
            (TokenKind::Const, _) | (TokenKind::Pub, TokenKind::Const) => {
                let const_decl = Const::parse(parser)?;
                Ok(Statement::ConstDeclaration(const_decl))
            }

            (TokenKind::Static, _) | (TokenKind::Pub, TokenKind::Static) => {
                let static_decl = Static::parse(parser)?;
                Ok(Statement::StaticDeclaration(static_decl))
            }

            // If the next tokens are `fn` or `pub fn`, it must be a function declaration.
            (TokenKind::Fn, _) | (TokenKind::Pub, TokenKind::Fn) => {
                let fn_decl = Function::parse(parser)?;
                Ok(Statement::FunctionDeclaration(fn_decl))
            }

            // If the first token is `{`, it must be a closure.
            (TokenKind::LeftBrace, _) => {
                let closure = Closure::parse(parser)?;
                Ok(Statement::Closure(closure))
            }

            // If the first token is `if`, it must be a conditional.
            (TokenKind::If, _) => {
                let cond = Conditional::parse(parser)?;
                Ok(Statement::Conditional(cond))
            }

            // If the first token is `match`, is must be a match statement.
            (TokenKind::Match, _) => Ok(Statement::Match(Match::parse(parser)?)),

            // If the first token is `for`, `while` or `loop`, it must be a loop.
            (TokenKind::For | TokenKind::While | TokenKind::Loop, _) => {
                let cond = Loop::parse(parser)?;
                Ok(Statement::Loop(Box::new(cond)))
            }

            // If the first token is `break`, it must be a break statement.
            (TokenKind::Break, _) => {
                let br = Break::parse(parser)?;
                Ok(Statement::Break(br))
            }

            // If the first token is `continue`, it must be a loop continue.
            (TokenKind::Continue, _) => {
                let cont = Continue::parse(parser)?;
                Ok(Statement::Continue(cont))
            }

            // If the first token is `impl`, it's the implementation of member functions for a type.
            (TokenKind::Impl, _) => {
                let impl_ = Impl::parse(parser)?;
                Ok(Statement::Impl(impl_))
            }

            // If the next tokens are `spec` or `pub spec`, it must be a spec declaration.
            (TokenKind::Spec, _) | (TokenKind::Pub, TokenKind::Spec) => {
                let spec_ = SpecType::parse(parser)?;
                Ok(Statement::SpecDeclaration(spec_))
            }

            // If the first token is `return`, it must be a return statement.
            (TokenKind::Return, _) => {
                let ret_token = parser.tokens.next().unwrap();
                let ret_token_span = ret_token.span;

                // If the next token is `}` or is on the following line, it's an empty return.
                // Otherwise, we expect an expression.
                let no_ret_val = match parser.tokens.peek_next() {
                    Some(Token {
                        kind: TokenKind::RightBrace,
                        ..
                    }) => true,

                    Some(Token { span, .. }) if span.end_pos.line > ret_token_span.end_pos.line => {
                        true
                    }

                    _ => false,
                };

                if no_ret_val {
                    return Ok(Statement::Return(Ret::new(None, ret_token_span)));
                }

                let expr = Expression::parse(parser)?;
                Ok(Statement::Return(Ret::new(
                    Some(expr.clone()),
                    parser.new_span(ret_token_span.start_pos, expr.span().end_pos),
                )))
            }

            // If the first token is `yield`, it must be a yield statement.
            (TokenKind::Yield, _) => {
                let yield_token = parser.tokens.next().unwrap();
                let start_pos = yield_token.span.start_pos;
                let expr = Expression::parse(parser)?;
                let end_pos = expr.span().end_pos;
                Ok(Statement::Yield(Yield::new(
                    expr,
                    parser.new_span(start_pos, end_pos),
                )))
            }

            // If the next tokens are `struct` or `pub struct`, it must be a struct declaration.
            (TokenKind::Struct, _) | (TokenKind::Pub, TokenKind::Struct) => {
                let struct_decl = StructType::parse(parser)?;
                Ok(Statement::StructDeclaration(struct_decl))
            }

            // If the next tokens are `enum` or `pub enum`, it must be an enum declaration.
            (TokenKind::Enum, _) | (TokenKind::Pub, TokenKind::Enum) => {
                let enum_decl = EnumType::parse(parser)?;
                Ok(Statement::EnumDeclaration(enum_decl))
            }

            // If the first token is `use`, it's a use (import).
            (TokenKind::Use, _) => {
                let use_mod = UsedMod::parse(parser)?;
                Ok(Statement::Use(use_mod))
            }

            // At this point the statement should be an assignment or a function call.
            (_, _) => {
                let start_pos = parser.current_position();
                let cursor = parser.tokens.cursor();

                // Parse the expression.
                let expr = Expression::parse(parser)?;

                // Check if this is an assignment.
                if parser.next_token_is_one_of(&vec![
                    TokenKind::Equal,
                    TokenKind::PlusEqual,
                    TokenKind::MinusEqual,
                    TokenKind::ForwardSlashEqual,
                    TokenKind::AsteriskEqual,
                    TokenKind::PercentEqual,
                    TokenKind::LogicalAndEqual,
                    TokenKind::LogicalOrEqual,
                    TokenKind::BitwiseAndEqual,
                    TokenKind::BitwiseOrEqual,
                    TokenKind::BitwiseXorEqual,
                    TokenKind::BitwiseLeftShiftEqual,
                    TokenKind::BitwiseRightShiftEqual,
                ]) {
                    // Parse the expression being assigned and return the variable
                    // assignment.
                    parser.tokens.set_cursor(cursor);
                    return Ok(Statement::VariableAssignment(VariableAssignment::parse(
                        parser,
                    )?));
                }

                // It's not an assignment, so it should be a function call.
                match expr {
                    Expression::FunctionCall(call) => Ok(Statement::FunctionCall(*call)),
                    _ => Err(ParseError::new(
                        ErrorKind::ExpectedStatement,
                        "expected statement, but found expression",
                        None,
                        parser.new_span(start_pos, parser.prev_position()),
                    )),
                }
            }
        }
    }
}
