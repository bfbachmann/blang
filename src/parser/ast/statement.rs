use std::collections::HashSet;
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
use crate::parser::ast::func_call::FunctionCall;
use crate::parser::ast::r#break::Break;
use crate::parser::ast::r#const::ConstBlock;
use crate::parser::ast::r#enum::EnumType;
use crate::parser::ast::r#impl::Impl;
use crate::parser::ast::r#loop::Loop;
use crate::parser::ast::r#struct::StructType;
use crate::parser::ast::r#use::UseBlock;
use crate::parser::ast::ret::Ret;
use crate::parser::ast::spec::Spec;
use crate::parser::ast::store::Store;
use crate::parser::ast::symbol::Symbol;
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
    Store(Store),
    FunctionDeclaration(Function),
    Closure(Closure),
    FunctionCall(FunctionCall),
    Conditional(Conditional),
    Loop(Loop),
    Break(Break),
    Continue(Continue),
    Return(Ret),
    StructDeclaration(StructType),
    EnumDeclaration(EnumType),
    ExternFns(Extern),
    Consts(ConstBlock),
    Impl(Impl),
    SpecDeclaration(Spec),
    Uses(UseBlock),
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
                write!(f, "{} = ...", var_assign.symbol)
            }
            Statement::Store(store) => {
                write!(f, "{} <- {}", store.dest_expr, store.source_expr)
            }
            Statement::FunctionDeclaration(func) => {
                write!(f, "{}", func.signature)
            }
            Statement::Closure(_) => {
                write!(f, "{{ ... }}")
            }
            Statement::FunctionCall(call) => {
                write!(f, "{}(...)", call.fn_symbol)
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
            Statement::Uses(use_block) => {
                write!(f, "{}", use_block)
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
            Statement::Store(store) => store.start_pos(),
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
            Statement::Uses(u) => u.start_pos(),
            Statement::Impl(i) => i.start_pos(),
            Statement::SpecDeclaration(t) => t.start_pos(),
        }
    }

    fn end_pos(&self) -> &Position {
        match self {
            Statement::VariableDeclaration(var_dec) => var_dec.end_pos(),
            Statement::VariableAssignment(var_assign) => var_assign.end_pos(),
            Statement::Store(store) => store.end_pos(),
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
            Statement::Uses(u) => u.end_pos(),
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
        // Try use the first two tokens to figure out what type of statement will follow. This works
        // because no valid statement can contain fewer than two tokens.
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

        match (first.unwrap(), second.unwrap()) {
            // If the first two tokens are "let <name>" or "let mut", it must be a variable
            // declaration.
            (
                Token {
                    kind: TokenKind::Let,
                    ..
                },
                Token {
                    kind: TokenKind::Identifier(_) | TokenKind::Mut,
                    ..
                },
            ) => {
                let var_decl = VariableDeclaration::from(tokens)?;
                Ok(Statement::VariableDeclaration(var_decl))
            }

            // If the first two tokens are "<identifier> =", it must be a variable assignment.
            (
                Token {
                    kind: TokenKind::Identifier(_),
                    ..
                },
                Token {
                    kind: TokenKind::Equal,
                    ..
                },
            ) => {
                let assign = VariableAssignment::from(tokens)?;
                Ok(Statement::VariableAssignment(assign))
            }

            // If the first token is `extern`, it's a set of external function declarations.
            (
                Token {
                    kind: TokenKind::Extern,
                    ..
                },
                _,
            ) => {
                let ext = Extern::from(tokens)?;
                Ok(Statement::ExternFns(ext))
            }

            // If the first token is `const`, it's a set of constant declarations.
            (
                Token {
                    kind: TokenKind::Const,
                    ..
                },
                _,
            ) => {
                let const_block = ConstBlock::from(tokens)?;
                Ok(Statement::Consts(const_block))
            }

            // If the first token is `fn`, it must be a function declaration.
            (
                Token {
                    kind: TokenKind::Fn,
                    ..
                },
                _,
            ) => {
                let fn_decl = Function::from(tokens)?;
                Ok(Statement::FunctionDeclaration(fn_decl))
            }

            // If the first token is `{`, it must be a closure.
            (
                Token {
                    kind: TokenKind::LeftBrace,
                    ..
                },
                _,
            ) => {
                let closure = Closure::from(tokens)?;
                Ok(Statement::Closure(closure))
            }

            // If the first two tokens are "<identifier>(", it must be a function call.
            (
                Token {
                    kind: TokenKind::Identifier(_),
                    ..
                },
                Token {
                    kind: TokenKind::LeftParen,
                    ..
                },
            ) => {
                let call = FunctionCall::from(tokens)?;
                Ok(Statement::FunctionCall(call))
            }

            // If the first token is `if`, it must be a conditional.
            (
                Token {
                    kind: TokenKind::If,
                    ..
                },
                _,
            ) => {
                let cond = Conditional::from(tokens)?;
                Ok(Statement::Conditional(cond))
            }

            // If the first token is `loop`, it must be a loop.
            (
                Token {
                    kind: TokenKind::Loop,
                    ..
                },
                _,
            ) => {
                let cond = Loop::from(tokens)?;
                Ok(Statement::Loop(cond))
            }

            // If the first token is `break`, it must be a break statement.
            (
                Token {
                    kind: TokenKind::Break,
                    ..
                },
                _,
            ) => {
                let br = Break::from(tokens)?;
                Ok(Statement::Break(br))
            }

            // If the first token is `continue`, it must be a loop continue.
            (
                Token {
                    kind: TokenKind::Continue,
                    ..
                },
                _,
            ) => {
                let cont = Continue::from(tokens)?;
                Ok(Statement::Continue(cont))
            }

            // If the first token is `impl`, it's the implementation of member functions for a type.
            (
                Token {
                    kind: TokenKind::Impl,
                    ..
                },
                _,
            ) => {
                let impl_ = Impl::from(tokens)?;
                Ok(Statement::Impl(impl_))
            }

            // If the first token is `spec`, it's a spec declaration.
            (
                Token {
                    kind: TokenKind::Spec,
                    ..
                },
                _,
            ) => {
                let spec_ = Spec::from(tokens)?;
                Ok(Statement::SpecDeclaration(spec_))
            }

            // If the first token is `return`, it must be a return statement.
            (
                Token {
                    kind: TokenKind::Return,
                    ..
                },
                _,
            ) => {
                let ret_token = tokens.next().unwrap();
                let ret_token_start = ret_token.start.clone();
                let ret_token_end = ret_token.end.clone();

                // If the next token is `}`, it's an empty return. Otherwise, we expect an
                // expression.
                if let Some(Token {
                    kind: TokenKind::RightBrace,
                    ..
                }) = tokens.peek_next()
                {
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
            (
                Token {
                    kind: TokenKind::Struct,
                    ..
                },
                _,
            ) => {
                let struct_decl = StructType::from(tokens)?;
                Ok(Statement::StructDeclaration(struct_decl))
            }

            // If the first token is `enum`, it must be a struct declaration.
            (
                Token {
                    kind: TokenKind::Enum,
                    ..
                },
                _,
            ) => {
                let enum_decl = EnumType::from(tokens)?;
                Ok(Statement::EnumDeclaration(enum_decl))
            }

            // If the first token is `use`, it's a use (imports) block.
            (
                Token {
                    kind: TokenKind::Use,
                    ..
                },
                _,
            ) => {
                let use_block = UseBlock::from(tokens)?;
                Ok(Statement::Uses(use_block))
            }

            // If the first two tokens are `<identifier>.`, it's a member access that can either be
            // an assignment to the member or a function call on the member.
            (
                Token {
                    kind: TokenKind::Identifier(_),
                    ..
                },
                Token {
                    kind: TokenKind::Dot,
                    ..
                },
            ) => {
                // Parse the expression.
                let cursor = tokens.cursor();
                let var = Symbol::from(tokens)?;

                // If the next token is `(`, it's a function call. Otherwise, it should be "=" for
                // member assignment.
                match Source::parse_expecting_any(
                    tokens,
                    HashSet::from([TokenKind::Equal, TokenKind::LeftParen]),
                )? {
                    Token {
                        kind: TokenKind::LeftParen,
                        ..
                    } => {
                        // Parse the function arguments and return the function call.
                        tokens.set_cursor(cursor);
                        let fn_call = FunctionCall::from(tokens)?;
                        Ok(Statement::FunctionCall(fn_call))
                    }

                    Token {
                        kind: TokenKind::Equal,
                        ..
                    } => {
                        // Parse the expression being assigned to the member and return the variable
                        // assignment.
                        let value = Expression::from(tokens)?;
                        let start_pos = var.start_pos.clone();
                        Ok(Statement::VariableAssignment(VariableAssignment::new(
                            var, value, start_pos,
                        )))
                    }

                    _ => unreachable!(),
                }
            }

            // At this point, the tokens must either represent a store statement or it's an invalid
            // statement.
            (_, _) => {
                // Try parse a store statement.
                match Store::from(tokens) {
                    Ok(store) => Ok(Statement::Store(store)),
                    Err(err) => Err(err),
                }
            }
        }
    }
}
