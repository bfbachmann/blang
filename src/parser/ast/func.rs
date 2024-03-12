use std::fmt;
use std::hash::Hash;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::parser::ast::arg::Argument;
use crate::parser::ast::closure::Closure;
use crate::parser::ast::func_sig::FunctionSignature;
use crate::parser::ast::lambda::LambdaDecl;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::ret::Ret;
use crate::parser::ast::statement::Statement;
use crate::parser::ast::tmpl_params::{TmplParam, TmplParams};
use crate::parser::error::ParseResult;

/// Represents a function declaration.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct Function {
    pub signature: FunctionSignature,
    pub body: Closure,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {{ ... }}", self.signature)
    }
}

impl Locatable for Function {
    fn start_pos(&self) -> &Position {
        &self.signature.start_pos()
    }

    fn end_pos(&self) -> &Position {
        &self.body.end_pos()
    }
}

impl Function {
    pub fn new(signature: FunctionSignature, body: Closure) -> Self {
        Function { signature, body }
    }

    /// Parses function declarations. Expects token sequences of the form
    ///
    ///      fn <fn_name>(<arg_name>: <arg_type>, ...): <return_type> { <body> }
    ///      fn <fn_name>(<arg_name>: <arg_type>, ...) { <body> }
    ///
    /// where
    ///  - `fn_name` is an identifier representing the name of the function
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    ///  - `return_type` is the type of the optional return type
    ///  - `body` is the body of the function
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
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
    pub fn from_anon(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // The first set of tokens should be the function signature.
        let sig = FunctionSignature::from_anon(tokens, true)?;

        // The remaining tokens should be the function body.
        let body = Closure::from(tokens)?;

        // Now that we have the function name and args, create the node.
        Ok(Function::new(sig, body))
    }

    /// Converts the given lambda into a function.
    pub fn from_lambda(lambda: LambdaDecl) -> Self {
        let start_pos = lambda.start_pos().clone();
        let end_pos = lambda.end_pos().clone();
        let mut tmpl_params = TmplParams::new_with_default_pos();
        let mut args = vec![];

        // Convert lambda arguments.
        for arg in lambda.args {
            let start_pos = arg.start_pos().clone();
            let end_pos = arg.end_pos().clone();

            let typ = match arg.maybe_type {
                Some(typ) => typ,
                None => {
                    let type_name = format!("{}Type", arg.name);
                    tmpl_params
                        .params
                        .push(TmplParam::new_with_default_pos(type_name.as_str()));
                    Type::new_unresolved(type_name.as_str())
                }
            };

            args.push(Argument::new(
                arg.name.as_str(),
                typ,
                arg.is_mut,
                start_pos,
                end_pos,
            ))
        }

        // Convert lambda return type.
        let ret_type_name = "R";
        tmpl_params
            .params
            .push(TmplParam::new_with_default_pos(ret_type_name));
        let ret_type = Type::new_unresolved(ret_type_name);

        // Convert the lambda expression to a function body containing only a return statement.
        let ret_start = lambda.expr.start_pos();
        let ret_end = lambda.expr.end_pos();
        let return_statement = Statement::Return(Ret::new(
            Some(lambda.expr.clone()),
            ret_start.clone(),
            ret_end.clone(),
        ));

        let signature =
            FunctionSignature::new_tmpl("", args, Some(ret_type), tmpl_params, start_pos, end_pos);

        let body = Closure::new(
            vec![return_statement],
            None,
            ret_start.clone(),
            ret_end.clone(),
        );

        Function { signature, body }
    }
}
