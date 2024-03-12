use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::statement::Statement;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;
use crate::{locatable_impl, util};
use std::hash::{Hash, Hasher};

/// Represents a closure, which is just a series of statements with their own scope.
#[derive(Debug, Clone, Eq)]
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

impl Hash for Closure {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.statements.hash(state);
        self.result.hash(state);
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
    ///     { <statement>; ... }
    ///
    /// where
    /// - `statement` is any valid statement (see `Statement::from`)
    /// - the semicolon is optional
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Record the closure starting position.
        let start_pos = Module::parse_expecting(tokens, TokenKind::LeftBrace)?.start;
        let end_pos: Position;

        // The following nodes should be statements separated by an optional ";".
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
