use std::collections::{HashSet, VecDeque};

use crate::lexer::kind::TokenKind;
use crate::lexer::token::Token;
use crate::parser::expr::Expression;
use crate::parser::program::Program;
use crate::parser::statement::Statement;
use crate::parser::ParseResult;
use crate::util;

/// Represents a closure, which is just a series of statements with their own scope.
#[derive(Debug, Clone)]
pub struct Closure {
    statements: Vec<Statement>,
    result: Option<Expression>,
}

impl PartialEq for Closure {
    fn eq(&self, other: &Self) -> bool {
        util::vectors_are_equal(&self.statements, &other.statements) && self.result == other.result
    }
}

impl Closure {
    pub fn new(statements: Vec<Statement>, result: Option<Expression>) -> Self {
        Closure { statements, result }
    }

    /// Parses closures. Expects token sequences of the form
    ///
    ///      { <statement>; ... }
    ///
    /// where
    /// - `statement` is any valid statement (see `Statement::from`)
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token should be "{".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::BeginClosure]))?;

        // The following nodes should be statements separated by ";".
        let mut statements = vec![];
        loop {
            match tokens.front() {
                // If the next token is "}", we've reached the end of the closure.
                Some(&Token {
                    kind: TokenKind::EndClosure,
                    ..
                }) => {
                    // We've reached the end of the closure. Pop the "}" and break the loop.
                    tokens.pop_front();
                    break;
                }

                // If the next token is ";", we've reached the end of the statement.
                Some(&Token {
                    kind: TokenKind::SemiColon,
                    ..
                }) => {
                    tokens.pop_front();
                }

                // If the next token is anything else, we expect it to be the beginning of a new
                // statement.
                _ => {
                    let statement = Statement::from(tokens)?;
                    statements.push(statement);
                }
            };
        }

        // If the last statement is an expression, we use it as the return type.
        // TODO.

        Ok(Closure::new(statements, None))
    }
}
