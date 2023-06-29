use crate::lexer::kind::TokenKind;
use crate::lexer::Token;
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
        let mut terminator = TokenKind::Comma;
        while terminator != TokenKind::CloseParen {
            // If the next token is ")", we're done parsing arguments.
            match tokens.front() {
                Some(&Token {
                    kind: TokenKind::CloseParen,
                    ..
                }) => {
                    tokens.pop_front();
                    break;
                }
                _ => {}
            }

            // Try parse the next argument as an expression.
            let (expr, term) = Expression::from(
                tokens,
                HashSet::from([TokenKind::Comma, TokenKind::CloseParen]),
            )?;
            args.push(expr);
            terminator = term.kind;
        }

        Ok(FunctionCall::new(fn_name.as_str(), args))
    }
}
