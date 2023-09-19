use std::collections::HashSet;
use std::fmt;

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::closure::Closure;
use crate::parser::cond::Conditional;
use crate::parser::cont::Continue;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::expr::Expression;
use crate::parser::func::Function;
use crate::parser::func_call::FunctionCall;
use crate::parser::program::Program;
use crate::parser::r#break::Break;
use crate::parser::r#loop::Loop;
use crate::parser::r#struct::StructType;
use crate::parser::ret::Ret;
use crate::parser::stream::Stream;
use crate::parser::var::Var;
use crate::parser::var_assign::VariableAssignment;
use crate::parser::var_dec::VariableDeclaration;

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
    Break(Break),
    Continue(Continue),
    Return(Ret),
    StructDeclaration(StructType),
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Statement::VariableDeclaration(var_dec) => {
                if let Some(typ) = &var_dec.typ {
                    write!(f, "let {}: {} = ...", typ, var_dec.name)
                } else {
                    write!(f, "let {} = ...", var_dec.name)
                }
            }
            Statement::VariableAssignment(var_assign) => {
                write!(f, "{} = ...", var_assign.var)
            }
            Statement::FunctionDeclaration(func) => {
                write!(f, "{}", func.signature)
            }
            Statement::Closure(_) => {
                write!(f, "{{ ... }}")
            }
            Statement::FunctionCall(call) => {
                write!(f, "{}(...)", call.fn_var)
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
                    ErrorKind::UnexpectedEOF,
                    "expected statement, but found EOF",
                    Some(token.clone()),
                    Position::default(),
                    Position::default(),
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
                let br = Break::from(tokens)?;
                Ok(Statement::Break(br))
            }

            // If the first token is "continue", it must be a loop continue.
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

            // If the first token is "return", it must be a return statement.
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

                // If the next token is "}", it's an empty return. Otherwise, we expect an
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

                let expr = Expression::from(tokens, false, false)?;
                Ok(Statement::Return(Ret::new(
                    Some(expr.clone()),
                    ret_token_start,
                    *expr.end_pos(),
                )))
            }

            // If the first token is "struct" it must be a struct declaration.
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

            // If the first two tokens are `<identifier>.`, it's a member access that can either be
            // an assignment to the member or or a function call on the member.
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
                // Parse the member access.
                let var = Var::from(tokens)?;

                // If the next token is "(", it's a function call. Otherwise, it should be "=" for
                // member assignment.
                match Program::parse_expecting(
                    tokens,
                    HashSet::from([TokenKind::Equal, TokenKind::LeftParen]),
                )? {
                    _token @ Token {
                        kind: TokenKind::LeftParen,
                        ..
                    } => {
                        // Parse the function arguments and return the function call.
                        tokens.rewind(1);
                        let fn_call = FunctionCall::from_args(tokens, var)?;
                        Ok(Statement::FunctionCall(fn_call))
                    }

                    Token {
                        kind: TokenKind::Equal,
                        ..
                    } => {
                        // Parse the expression being assigned to the member and return the variable
                        // assignment.
                        let value = Expression::from(tokens, false, false)?;
                        let start_pos = var.start_pos.clone();
                        Ok(Statement::VariableAssignment(VariableAssignment::new(
                            var, value, start_pos,
                        )))
                    }

                    _ => unreachable!(),
                }
            }

            // If the tokens are anything else, we error because it's an invalid statement.
            (&ref token, _) => Err(ParseError::new_with_token(
                ErrorKind::InvalidStatement,
                "invalid statement",
                token.clone(),
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::token::Token;
    use crate::parser::statement::Statement;
    use crate::parser::stream::Stream;

    #[test]
    fn parse_var_assignment() {
        let tokens = Token::tokenize_line("let thing: i64 = 234", 0).expect("should not error");
        Statement::from(&mut Stream::from(tokens)).expect("should not error");
    }
}
