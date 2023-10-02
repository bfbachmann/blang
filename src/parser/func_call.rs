use std::fmt;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::expr::Expression;
use crate::parser::program::Program;
use crate::parser::stream::Stream;
use crate::parser::var::Var;
use crate::util;

/// Represents the calling of a function.
#[derive(Debug, Clone)]
pub struct FunctionCall {
    /// Should either be the name of the function, a function variable name, or an access of a
    /// variable's function member.
    pub fn_var: Var,
    pub args: Vec<Expression>,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl PartialEq for FunctionCall {
    fn eq(&self, other: &Self) -> bool {
        self.fn_var == other.fn_var
            && util::vecs_eq(&self.args, &other.args)
            && self.start_pos == other.start_pos
            && self.end_pos == other.end_pos
    }
}

impl fmt::Display for FunctionCall {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}(", self.fn_var)?;

        for (i, arg) in self.args.iter().enumerate() {
            write!(f, "{}", arg)?;

            if i < self.args.len() - 1 {
                write!(f, ", ")?;
            }
        }

        write!(f, ")")
    }
}

impl Locatable for FunctionCall {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl FunctionCall {
    /// Creates a new function call with default (zero) start and end positions.
    #[cfg(test)]
    pub fn new_with_default_pos(fn_name: &str, args: Vec<Expression>) -> Self {
        FunctionCall {
            fn_var: Var::new_with_default_pos(fn_name),
            args,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Creates a new function call.
    #[cfg(test)]
    pub fn new(fn_var: Var, args: Vec<Expression>, start_pos: Position, end_pos: Position) -> Self {
        FunctionCall {
            fn_var,
            args,
            start_pos,
            end_pos,
        }
    }

    /// Parses function arguments from the given token sequence and returns a new function call
    /// with the parsed arguments and the given function reference.
    pub fn from_args(tokens: &mut Stream<Token>, fn_var: Var) -> ParseResult<Self> {
        // Get the start position of the function call in the source file.
        let start_pos = fn_var.start_pos().clone();
        let end_pos: Position;

        // The next token should be `(`.
        Program::parse_expecting(tokens, TokenKind::LeftParen)?;

        // The remaining tokens should be expressions representing argument values separated by `,`
        // and ending in `)`.
        let mut args = vec![];
        loop {
            match tokens.peek_next() {
                // If the next token is `)`, we break because we're done parsing arguments.
                Some(&Token {
                    kind: TokenKind::RightParen,
                    ..
                }) => {
                    // Pop the `)` and set the end position of this function call in the source
                    // file.
                    end_pos = tokens.next().unwrap().end;
                    break;
                }

                // If the next token is `,`, we'll make sure that we've already parsed at least one
                // argument because the comma should only come after an argument.
                Some(
                    comma @ &Token {
                        kind: TokenKind::Comma,
                        ..
                    },
                ) => {
                    if args.len() == 0 {
                        return Err(ParseError::new_with_token(
                            ErrorKind::ExpectedExprOrCloseParen,
                            format!(r#"expected expression or ")", but found "{}"#, &comma)
                                .as_str(),
                            comma.clone(),
                        ));
                    }

                    // Pop the `,`.
                    tokens.next();

                    // If the next token is `)`, we break. We're allowing arguments to end in ",)"
                    // to account for cases where function call arguments are broken over
                    // multiple lines and the user wishes to end the last argument with a `,`.
                    if let Some(&Token {
                        kind: TokenKind::RightParen,
                        ..
                    }) = tokens.peek_next()
                    {
                        // Pop the `)` and set the end position of this function call in the source
                        // file.
                        end_pos = tokens.next().unwrap().end;
                        break;
                    }
                }

                None => {
                    return Err(ParseError::new(
                        ErrorKind::UnexpectedEOF,
                        "expected argument, but found EOF",
                        None,
                        start_pos,
                        Program::current_position(tokens),
                    ));
                }

                // If the next token is not `,` or `)`, we assume that it's the beginning of an
                // expression that represents the next argument.
                _ => {}
            }

            let expr = Expression::from(tokens, true)?;
            args.push(expr);
        }

        Ok(FunctionCall {
            fn_var,
            args,
            start_pos,
            end_pos,
        })
    }

    /// Parse a single (i.e. not chained) function call. Expects token sequences of the form
    ///
    ///     <fn_var>(<arg>, ...)
    ///
    /// where
    ///  - `fn_var` is the name of the function being called or a chained member access ending in
    ///     the function member (e.g `var.field_member.fn_member()`, see `Var::from`).
    ///  - `arg` is some expression that evaluates to the argument value
    pub fn from_single(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // The first token should be the function identifier (either just a function name or a
        // member access). We parse this the same way we parse a regular variable.
        let fn_var = Var::from(tokens)?;

        // Parse the function arguments.
        FunctionCall::from_args(tokens, fn_var)
    }

    /// Parses a chain of function calls. Expects token sequences of the forms
    ///
    ///     <var>()
    ///     <var>()()...
    ///     <var>().<fn_call>...
    ///
    /// where
    ///  - `var` is any variable that is a function (see `Var::from`)
    ///  - `<fn_call>` is any series of function calls accepted by this function.
    ///
    /// The first example is a single function call. The second is one where the return type
    /// of the first call in the chain is itself a function that is being called. The third is one
    /// where chained calls are being made on some member of the return value of the first call.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Parse the first function call.
        let mut calls = vec![FunctionCall::from_single(tokens)?];

        // Try parse chained function calls after the first. There may be none.
        loop {
            match tokens.peek_next() {
                // The next function may be called on a member of the return value of the last one,
                // in which case we expect the next token to be `.`.
                Some(Token {
                    kind: TokenKind::Dot,
                    ..
                }) => {
                    tokens.next();
                    calls.push(FunctionCall::from_single(tokens)?);
                }

                // The next function may be called directly on the return value of the last one
                // if the return value is a function. In this case, we expect the next token to be
                // `(`.
                Some(Token {
                    kind: TokenKind::LeftParen,
                    ..
                }) => {
                    let token = tokens.next().unwrap();
                    let start_pos = token.start;
                    let end_pos = token.end;

                    calls.push(FunctionCall::from_args(
                        tokens,
                        Var::new("", start_pos, end_pos),
                    )?);
                }

                // If the token is anything else, we assume we're done checking the call chain.
                _ => {
                    break;
                }
            };
        }

        // Convert the chain of calls into nested calls and return the outermost call.
        let mut maybe_last_call: Option<FunctionCall> = None;
        while !calls.is_empty() {
            // Get the next call at the front of the chain.
            let mut call = calls.remove(0);

            // Add the return value of the last call as the first argument of this call.
            if let Some(last_call) = maybe_last_call {
                call.args.insert(0, Expression::FunctionCall(last_call));
            }

            // Track the result of this call so it can be passed as the first argument of the next
            // one, or returned if this is the last call in the chain.
            maybe_last_call = Some(call);
        }

        Ok(maybe_last_call.unwrap())
    }

    /// Returns true if the function call is directly to a function (i.e. doesn't happen via member
    /// access) and the called function has the given name.
    pub fn has_fn_name(&self, name: &str) -> bool {
        self.fn_var.var_name == name && self.fn_var.member_access.is_none()
    }
}
