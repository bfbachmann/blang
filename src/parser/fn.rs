use crate::lexer::kind::TokenKind;
use crate::lexer::Token;
use crate::parser::arg::Argument;
use crate::parser::closure::Closure;
use crate::parser::error::ParseError;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::{ParseResult, Program};
use std::collections::{HashSet, VecDeque};

/// Represents a function declaration.
#[derive(Debug, PartialEq)]
pub struct Function {
    signature: FunctionSignature,
    body: Closure,
}

impl Function {
    pub fn new(signature: FunctionSignature, body: Closure) -> Self {
        Function { signature, body }
    }

    /// Parses function declarations. Expects token sequences of the form
    ///
    ///      fn <fn_name>(<arg_type> <arg_name>, ...): <return_type> { <body> }
    ///      fn <fn_name>(<arg_type> <arg_name>, ...) { <body> }
    ///
    /// where
    ///  - `fn_name` is an identifier representing the name of the function
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    ///  - `body` is the body of the function
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first set of tokens should be the function signature.
        let sig = FunctionSignature::from(tokens)?;

        // The remaining tokens should be the function body.
        let body = Closure::from(tokens)?;

        // Now that we have the function name and args, create the node.
        Ok(Function::new(sig, body))
    }

    /// Parses anonymous function declarations. Expects token sequences of the forms
    ///
    ///      fn (<arg_type> <arg_name>, ...): <return_type> { <body> }
    ///      fn (<arg_type> <arg_name>, ...) { <body> }
    ///
    /// where
    ///  - `fn_name` is an identifier representing the name of the function
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    ///  - `body` is the body of the function
    pub fn from_anon(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first set of tokens should be the function signature.
        let sig = FunctionSignature::from_anon(tokens)?;

        // The remaining tokens should be the function body.
        let body = Closure::from(tokens)?;

        // Now that we have the function name and args, create the node.
        Ok(Function::new(sig, body))
    }

    /// Parses argument declarations in function declarations. Expects token sequences of the form
    ///
    ///      (<arg_type> <arg_name>, ...)
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    pub fn arg_declarations_from(tokens: &mut VecDeque<Token>) -> ParseResult<Vec<Argument>> {
        // The first token should be the opening parenthesis.
        Program::parse_expecting(tokens, HashSet::from([TokenKind::OpenParen]))?;

        // The next token(s) should be arguments or a closing parenthesis.
        let mut args = vec![];
        loop {
            // The next token should be an argument, or ")".
            let token = tokens.pop_front();
            match token {
                Some(Token {
                    kind: TokenKind::CloseParen,
                    ..
                }) => {
                    // We're done assembling arguments.
                    break;
                }
                Some(Token {
                    kind: TokenKind::String | TokenKind::Int | TokenKind::Bool | TokenKind::Function,
                    ..
                }) => {
                    // The next few tokens represent an argument.
                    tokens.push_front(token.unwrap());
                    let arg = Argument::from(tokens)?;
                    args.push(arg);
                }
                None => {
                    return Err(ParseError::new(
                        r#"Expected argument or ")" (end of function arguments)"#,
                        None,
                    ))
                }
                Some(other) => {
                    return Err(ParseError::new(
                        format!(
                            r#"Expected argument or ")" (end of function arguments), but got "{}""#,
                            other
                        )
                        .as_str(),
                        Some(other),
                    ))
                }
            };

            // After the argument, the next token should be "," or ")".
            let kind = Program::parse_expecting(
                tokens,
                HashSet::from([TokenKind::Comma, TokenKind::CloseParen]),
            )?;
            match kind {
                TokenKind::Comma => {} // Nothing to do here. Just move onto the next arg.
                TokenKind::CloseParen => break, // We're done parsing args.
                _ => panic!("this should be impossible"),
            }
        }

        Ok(args)
    }
}
