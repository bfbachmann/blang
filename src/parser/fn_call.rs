use crate::lexer::kind::TokenKind;
use crate::lexer::Token;
use crate::parser::error::ParseError;
use crate::parser::expr::Expression;
use crate::parser::{ParseResult, Program};
use crate::util;
use std::collections::{HashSet, VecDeque};

/// Represents the calling of a function.
#[derive(Debug)]
pub struct FunctionCall {
    fn_name: String,
    args: Vec<Expression>,
}

impl PartialEq for FunctionCall {
    fn eq(&self, other: &Self) -> bool {
        self.fn_name == other.fn_name && util::vectors_are_equal(&self.args, &other.args)
    }
}

impl FunctionCall {
    pub fn new(fn_name: &str, args: Vec<Expression>) -> Self {
        FunctionCall {
            fn_name: fn_name.to_string(),
            args,
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
        // The first token should be the function name.
        let fn_name = Program::parse_identifier(tokens)?;

        // The next token should be "(".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::OpenParen]))?;

        // The remaining tokens should be expressions representing argument values separated by ","
        // and ending in ")".
        let mut args = vec![];
        loop {
            match tokens.front() {
                // If the next token is ")", we break because we're done parsing arguments.
                Some(&Token {
                    kind: TokenKind::CloseParen,
                    ..
                }) => {
                    // Pop the ")".
                    tokens.pop_front();
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
                        return Err(ParseError::new(
                            format!(r#"Expected expression or ")", but got "{}"#, comma).as_str(),
                            Some(comma.clone()),
                        ));
                    }

                    // Pop the ",".
                    tokens.pop_front();
                }

                None => {
                    return Err(ParseError::new("Unexpected end of arguments", None));
                }

                // If the next token is not "," or ")", we assume that it's the beginning of an
                // expression that represents the next argument.
                _ => {}
            }

            let expr = Expression::from(tokens)?;
            args.push(expr);
        }

        Ok(FunctionCall::new(fn_name.as_str(), args))
    }
}
