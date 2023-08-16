use std::collections::{HashSet, VecDeque};
use std::fmt;

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::expr::Expression;
use crate::parser::program::Program;
use crate::util;

/// Represents the calling of a function.
#[derive(Debug, Clone)]
pub struct FunctionCall {
    pub fn_name: String,
    pub args: Vec<Expression>,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl PartialEq for FunctionCall {
    fn eq(&self, other: &Self) -> bool {
        self.fn_name == other.fn_name
            && util::vectors_are_equal(&self.args, &other.args)
            && self.start_pos == other.start_pos
            && self.end_pos == other.end_pos
    }
}

impl fmt::Display for FunctionCall {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}(", self.fn_name)?;

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
            fn_name: fn_name.to_string(),
            args,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Creates a new function call.
    pub fn new(
        fn_name: &str,
        args: Vec<Expression>,
        start_pos: Position,
        end_pos: Position,
    ) -> Self {
        FunctionCall {
            fn_name: fn_name.to_string(),
            args,
            start_pos,
            end_pos,
        }
    }

    /// Parses function calls. Expects token sequences of the form
    ///
    ///     <name>(<arg>, ...)
    ///
    /// where
    ///  - `name` is the name of the function being called
    ///  - `arg` is some expression that evaluates to the argument value
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // Get the start position of the function call in the source file.
        let start_pos = Program::current_position(tokens);
        let end_pos: Position;

        // The first token should be the function name.
        let fn_name = Program::parse_identifier(tokens)?;

        // The next token should be "(".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::LeftParen]))?;

        // The remaining tokens should be expressions representing argument values separated by ","
        // and ending in ")".
        let mut args = vec![];
        loop {
            match tokens.front() {
                // If the next token is ")", we break because we're done parsing arguments.
                Some(&Token {
                    kind: TokenKind::RightParen,
                    ..
                }) => {
                    // Pop the ")" and set the end position of this function call in the source
                    // file.
                    end_pos = tokens.pop_front().unwrap().end;
                    break;
                }

                // If the next token is ",", we'll make sure that we've already parsed at least one
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

                    // Pop the ",".
                    tokens.pop_front();

                    // If the next token is ")", we break. We're allowing arguments to end in ",)"
                    // a to account for cases where function call arguments are broken over
                    // multiple lines and the user wishes to end the last argument with a ",".
                    if let Some(&Token {
                        kind: TokenKind::RightParen,
                        ..
                    }) = tokens.front()
                    {
                        // Pop the ")" and set the end position of this function call in the source
                        // file.
                        end_pos = tokens.pop_front().unwrap().end;
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

                // If the next token is not "," or ")", we assume that it's the beginning of an
                // expression that represents the next argument.
                _ => {}
            }

            let expr = Expression::from(tokens, true, false)?;
            args.push(expr);
        }

        Ok(FunctionCall::new(
            fn_name.as_str(),
            args,
            start_pos,
            end_pos,
        ))
    }
}
