use std::collections::VecDeque;
use std::fmt;

use crate::lexer::token::Token;
use crate::parser::closure::Closure;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::ParseResult;

/// Represents a function declaration.
#[derive(Debug, PartialEq, Clone)]
pub struct Function {
    pub signature: FunctionSignature,
    pub body: Closure,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {{ ... }}", self.signature)
    }
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
        let sig = FunctionSignature::from_anon(tokens, true)?;

        // The remaining tokens should be the function body.
        let body = Closure::from(tokens)?;

        // Now that we have the function name and args, create the node.
        Ok(Function::new(sig, body))
    }
}
