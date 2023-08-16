use std::collections::{HashSet, VecDeque};

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::error::ParseResult;
use crate::parser::expr::Expression;
use crate::parser::program::Program;
use crate::parser::statement::Statement;
use crate::util;

/// Represents a closure, which is just a series of statements with their own scope.
#[derive(Debug, Clone)]
pub struct Closure {
    pub statements: Vec<Statement>,
    pub result: Option<Expression>,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl PartialEq for Closure {
    fn eq(&self, other: &Self) -> bool {
        util::vectors_are_equal(&self.statements, &other.statements)
            && self.result == other.result
            && self.start_pos == other.start_pos
            && self.end_pos == other.end_pos
    }
}

impl Locatable for Closure {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl Closure {
    /// Creates a new empty closure with default (zero) start and end positions.
    #[cfg(test)]
    pub fn new_empty() -> Self {
        Closure {
            statements: vec![],
            result: None,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Creates a new closure.
    pub fn new(
        statements: Vec<Statement>,
        result: Option<Expression>,
        start_pos: Position,
        end_pos: Position,
    ) -> Self {
        Closure {
            statements,
            result,
            start_pos,
            end_pos,
        }
    }

    /// Parses closures. Expects token sequences of the form
    ///
    ///      { <statement>; ... }
    ///
    /// where
    /// - `statement` is any valid statement (see `Statement::from`)
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // Record the closure starting position.
        let start_pos = Program::current_position(tokens);
        let end_pos: Position;

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
                    let end_token = tokens.pop_front().unwrap();

                    // Record the closure ending position.
                    end_pos = end_token.end;
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
        // TODO

        Ok(Closure::new(statements, None, start_pos, end_pos))
    }
}
