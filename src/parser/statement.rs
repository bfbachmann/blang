use crate::lexer::kind::TokenKind;
use crate::lexer::Token;
use crate::parser::closure::Closure;
use crate::parser::cond::Conditional;
use crate::parser::error::ParseError;
use crate::parser::expr::Expression;
use crate::parser::fn_call::FunctionCall;
use crate::parser::r#fn::Function;
use crate::parser::r#loop::Loop;
use crate::parser::var_assign::VariableAssignment;
use crate::parser::var_dec::VariableDeclaration;
use crate::parser::ParseResult;
use std::collections::{HashSet, VecDeque};

/// Represents a statement.
#[derive(Debug, PartialEq)]
pub enum Statement {
    VariableDeclaration(VariableDeclaration),
    VariableAssignment(VariableAssignment),
    FunctionDeclaration(Function),
    Closure(Closure),
    Expression(Expression),
    FunctionCall(FunctionCall),
    Conditional(Conditional),
    Loop(Loop),
    Break,
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
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // Try use the first two tokens to figure out what type of statement will follow. This works
        // because no valid statement can contain fewer than two tokens.
        let (first, second) = (tokens.front(), tokens.get(1));
        match (&first, &second) {
            (None, None) => return Err(ParseError::new("Unexpected end of of statement", None)),
            (None, Some(&ref token)) | (Some(&ref token), None) => {
                return Err(ParseError::new(
                    "Unexpected end of of statement",
                    Some(token.clone()),
                ))
            }
            _ => {}
        }

        match (
            first.expect("first token should not be None"),
            second.expect("second token should not be None"),
        ) {
            // If the first token is a type, it must be a variable declaration.
            (
                Token {
                    kind: TokenKind::Int | TokenKind::String | TokenKind::Bool,
                    ..
                },
                _,
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

            // If the first token is "fn", it must be a function declaration.
            (
                Token {
                    kind: TokenKind::Function,
                    ..
                },
                _,
            ) => {
                let fn_decl = Function::from(tokens)?;
                Ok(Statement::FunctionDeclaration(fn_decl))
            }

            // If the first token is "{", it must be a closure.
            (
                Token {
                    kind: TokenKind::BeginClosure,
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
                    kind: TokenKind::OpenParen,
                    ..
                },
            ) => {
                let call = FunctionCall::from(tokens)?;
                Ok(Statement::FunctionCall(call))
            }

            // If the first token is "if", it must be a conditional.
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

            // If the first token is "loop", it must be a loop.
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

            // If the first token is "break", it must be a break statement.
            (
                Token {
                    kind: TokenKind::Break,
                    ..
                },
                _,
            ) => {
                tokens.pop_front();
                Ok(Statement::Break)
            }

            // If the tokens are anything else, we'll try parse as an expression.
            (_, _) => {
                let (expr, _) = Expression::from(tokens, HashSet::from([TokenKind::SemiColon]))?;
                Ok(Statement::Expression(expr))
            }
        }
    }
}
