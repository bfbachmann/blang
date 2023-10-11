use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::error::ParseResult;
use crate::parser::expr::Expression;
use crate::parser::program::Program;
use crate::parser::statement::Statement;
use crate::parser::stream::Stream;
use crate::{locatable_impl, util};

/// Represents a closure, which is just a series of statements with their own scope.
#[derive(Debug, Clone)]
pub struct Closure {
    pub statements: Vec<Statement>,
    pub result: Option<Expression>,
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for Closure {
    fn eq(&self, other: &Self) -> bool {
        util::vecs_eq(&self.statements, &other.statements)
            && self.result == other.result
            && self.start_pos == other.start_pos
            && self.end_pos == other.end_pos
    }
}

locatable_impl!(Closure);

impl Closure {
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
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Record the closure starting position.
        let start_pos = Program::current_position(tokens);
        let end_pos: Position;

        // The first token should be `{`.
        Program::parse_expecting(tokens, TokenKind::LeftBrace)?;

        // The following nodes should be statements separated by ";".
        let mut statements = vec![];
        loop {
            match tokens.peek_next() {
                // If the next token is `}`, we've reached the end of the closure.
                Some(&Token {
                    kind: TokenKind::RightBrace,
                    ..
                }) => {
                    // We've reached the end of the closure. Move past `}` and break the loop.
                    let end_token = tokens.next().unwrap();

                    // Record the closure ending position.
                    end_pos = end_token.end;
                    break;
                }

                // If the next token is ";", we've reached the end of the statement.
                Some(&Token {
                    kind: TokenKind::SemiColon,
                    ..
                }) => {
                    tokens.next();
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
