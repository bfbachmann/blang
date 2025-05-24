use std::fmt;

use crate::lexer::pos::Span;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::closure::Closure;
use crate::parser::ast::func_sig::FunctionSignature;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a function declaration.
#[derive(Debug, PartialEq, Clone)]
pub struct Function {
    pub signature: FunctionSignature,
    pub body: Closure,
    pub is_pub: bool,
    pub span: Span,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {{ ... }}", self.signature)
    }
}

locatable_impl!(Function);

impl Function {
    pub fn new(signature: FunctionSignature, body: Closure, is_pub: bool) -> Self {
        let sig_span = &signature.span;

        Function {
            span: Span {
                file_id: sig_span.file_id,
                start_pos: sig_span.start_pos,
                end_pos: body.span().end_pos,
            },
            signature,
            body,
            is_pub,
        }
    }

    /// Parses function declarations. Expects token sequences of the form
    ///
    ///      pub fn <fn_name>(<arg_name>: <arg_type>, ...) -> <return_type> { <body> }
    ///      pub fn <fn_name>(<arg_name>: <arg_type>, ...) { <body> }
    ///
    /// where
    ///  - `fn_name` is an identifier representing the name of the function
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    ///  - `body` is the body of the function
    ///  - `pub` is optional.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        let is_pub = parser.parse_optional(TokenKind::Pub).is_some();

        // The first set of tokens should be the function signature.
        let sig = FunctionSignature::parse(parser)?;

        // The remaining tokens should be the function body.
        let body = Closure::parse(parser)?;

        // Now that we have the function name and args, create the node.
        Ok(Function::new(sig, body, is_pub))
    }

    /// Parses anonymous function declarations. Expects token sequences of the forms
    ///
    ///      fn (<arg_type> <arg_name>, ...) -> <return_type> { <body> }
    ///      fn (<arg_type> <arg_name>, ...) { <body> }
    ///
    /// where
    ///  - `fn_name` is an identifier representing the name of the function
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    ///  - `body` is the body of the function
    pub fn parse_anon(parser: &mut FileParser) -> ParseResult<Self> {
        // The first set of tokens should be the function signature.
        let sig = FunctionSignature::parse_anon(parser, true)?;

        // The remaining tokens should be the function body.
        let body = Closure::parse(parser)?;

        // Now that we have the function name and args, create the node.
        Ok(Function::new(sig, body, false))
    }
}
