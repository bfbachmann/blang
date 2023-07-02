use std::collections::{HashSet, VecDeque};

use crate::lexer::kind::TokenKind;
use crate::lexer::token::Token;
use crate::parser::arg::Argument;
use crate::parser::error::ParseError;
use crate::parser::program::Program;
use crate::parser::{ParseResult, Type};
use crate::util;

/// Represents the name, arguments, and return type of a function. Anonymous functions have empty
/// names.
#[derive(Debug)]
pub struct FunctionSignature {
    name: String,
    args: Vec<Argument>,
    return_type: Option<Type>,
}

impl PartialEq for FunctionSignature {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && util::vectors_are_equal(&self.args, &other.args)
            && self.return_type == other.return_type
    }
}

impl FunctionSignature {
    pub fn new(name: &str, args: Vec<Argument>, return_type: Option<Type>) -> Self {
        FunctionSignature {
            name: name.to_string(),
            args,
            return_type,
        }
    }

    pub fn new_anon(args: Vec<Argument>, return_type: Option<Type>) -> Self {
        FunctionSignature {
            name: "".to_string(),
            args,
            return_type,
        }
    }

    /// Parses function signatures. Expects token sequences of the forms
    ///
    ///      fn <fn_name>(<arg_type> <arg_name>, ...): (<return_type>, ...)
    ///      fn <fn_name>(<arg_type> <arg_name>, ...)
    ///
    /// where
    ///  - `fn_name` is an identifier representing the name of the function
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token should be "fn".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Function]))?;

        // The second token should be an identifier that represents the function name.
        let fn_name = Program::parse_identifier(tokens)?;

        // The next tokens should represent function arguments and optional return type.
        let fn_sig = FunctionSignature::from_args_and_return(tokens, true)?;

        Ok(FunctionSignature::new(
            fn_name.as_str(),
            fn_sig.args,
            fn_sig.return_type,
        ))
    }

    /// Parses anonymous function signatures. If `named` is true, expects token sequences of the
    /// forms
    ///
    ///      fn (<arg_type> <arg_name>, ...): <return_type>
    ///      fn (<arg_type> <arg_name>, ...)
    ///
    /// Otherwise, expects token sequences of the forms
    ///
    ///      fn (<arg_type>, ...): <return_type>
    ///      fn (<arg_type>, ...)
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    pub fn from_anon(tokens: &mut VecDeque<Token>, named: bool) -> ParseResult<Self> {
        // The first token should be "fn".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Function]))?;

        // The next tokens should represent function arguments followed by the return type.
        let fn_sig = FunctionSignature::from_args_and_return(tokens, named)?;
        Ok(fn_sig)
    }

    /// Parses function arguments and return value from a function signature. If `named` is true,
    /// expects token sequences of the forms
    ///
    ///     (<arg_type> <arg_name>, ...): <return_type>
    ///     (<arg_type> <arg_name>, ...)
    ///
    /// Otherwise, expects token sequences of the form
    ///
    ///     (<arg_type>, ...)
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return value
    fn from_args_and_return(tokens: &mut VecDeque<Token>, named: bool) -> ParseResult<Self> {
        // The next tokens should represent function arguments.
        let args = FunctionSignature::arg_declarations_from(tokens, named)?;

        // The next token should be ":" if there is a return type. Otherwise, there is no return
        // type and we're done.
        let mut return_type = None;
        match tokens.front() {
            Some(Token {
                kind: TokenKind::Colon,
                ..
            }) => {
                // Remove the ":" and parse the return type.
                tokens.pop_front();
                return_type = Some(Type::from(tokens)?);
            }
            _ => {}
        }

        Ok(FunctionSignature::new_anon(args, return_type))
    }

    /// Parses argument declarations in function declarations. If `named` is true, expects token
    /// sequences of the form
    ///
    ///      (<arg_type> <arg_name>, ...)
    ///
    /// Otherwise, expects token sequences of the form
    ///
    ///      (<arg_type>, ...)
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    fn arg_declarations_from(
        tokens: &mut VecDeque<Token>,
        named: bool,
    ) -> ParseResult<Vec<Argument>> {
        // The first token should be the opening parenthesis.
        Program::parse_expecting(tokens, HashSet::from([TokenKind::LeftParen]))?;

        // The next token(s) should be arguments or a closing parenthesis.
        let mut args = vec![];
        loop {
            // The next token should be an argument, or ")".
            let token = tokens.pop_front();
            match token {
                Some(Token {
                    kind: TokenKind::RightParen,
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
                    let arg = if named {
                        Argument::from(tokens)?
                    } else {
                        Argument::unnamed_from(tokens)?
                    };
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
                HashSet::from([TokenKind::Comma, TokenKind::RightParen]),
            )?;
            match kind {
                TokenKind::Comma => {} // Nothing to do here. Just move onto the next arg.
                TokenKind::RightParen => break, // We're done parsing args.
                _ => panic!("this should be impossible"),
            }
        }

        Ok(args)
    }
}
