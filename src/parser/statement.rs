use std::collections::VecDeque;

use crate::lexer::kind::TokenKind;
use crate::lexer::token::Token;
use crate::parser::closure::Closure;
use crate::parser::cond::Conditional;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::expr::Expression;
use crate::parser::func::Function;
use crate::parser::func_call::FunctionCall;
use crate::parser::r#loop::Loop;
use crate::parser::var_assign::VariableAssignment;
use crate::parser::var_dec::VariableDeclaration;
use crate::parser::ParseResult;

use std::fmt;

/// Represents a statement.
#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    VariableDeclaration(VariableDeclaration),
    VariableAssignment(VariableAssignment),
    FunctionDeclaration(Function),
    Closure(Closure),
    FunctionCall(FunctionCall),
    Conditional(Conditional),
    Loop(Loop),
    Break,
    Return(Option<Expression>),
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Statement::VariableDeclaration(var_dec) => {
                write!(
                    f,
                    "variable declaration {} {} = ...",
                    var_dec.typ, var_dec.name
                )
            }
            Statement::VariableAssignment(var_assign) => {
                write!(f, "variable assignment {} = ...", var_assign.name)
            }
            Statement::FunctionDeclaration(func) => {
                write!(f, "function declaration {}", func.signature)
            }
            Statement::Closure(_) => {
                write!(f, "closure")
            }
            Statement::FunctionCall(call) => {
                write!(f, "function call {}(...)", call.fn_name)
            }
            Statement::Conditional(_) => {
                write!(f, "conditional")
            }
            Statement::Loop(_) => {
                write!(f, "loop")
            }
            Statement::Break => {
                write!(f, "break")
            }
            Statement::Return(_) => {
                write!(f, "return")
            }
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
    ///  - return (of the form `return <expr>` where `expr` is an expression)
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // Try use the first two tokens to figure out what type of statement will follow. This works
        // because no valid statement can contain fewer than two tokens.
        let (first, second) = (tokens.front(), tokens.get(1));
        match (&first, &second) {
            (None, None) => {
                return Err(ParseError::new(
                    ErrorKind::UnexpectedEndOfStatement,
                    "Unexpected end of of statement",
                    None,
                ))
            }
            (None, Some(&ref token)) | (Some(&ref token), None) => {
                return Err(ParseError::new(
                    ErrorKind::UnexpectedEndOfStatement,
                    "Unexpected end of of statement",
                    Some(token.clone()),
                ))
            }
            _ => {}
        }

        match (first.unwrap(), second.unwrap()) {
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
                    kind: TokenKind::LeftParen,
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

            // If the first token is "return", it must be a return statement.
            (
                Token {
                    kind: TokenKind::Return,
                    ..
                },
                _,
            ) => {
                tokens.pop_front();

                // If the next token is "}", it's an empty return. Otherwise, we expect an
                // expression.
                if let Some(Token {
                    kind: TokenKind::EndClosure,
                    ..
                }) = tokens.front()
                {
                    return Ok(Statement::Return(None));
                }

                let expr = Expression::from(tokens, false)?;
                Ok(Statement::Return(Some(expr)))
            }

            // If the tokens are anything else, we error because it's an invalid statement.
            (&ref token, _) => Err(ParseError::new(
                ErrorKind::InvalidStatement,
                "Invalid statement",
                Some(token.clone()),
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::token::Token;
    use crate::parser::statement::Statement;

    #[test]
    fn parse_var_assignment() {
        let mut tokens = Token::tokenize_line("int thing = 234", 0).expect("should not error");
        Statement::from(&mut tokens).expect("should not error");
    }
}
