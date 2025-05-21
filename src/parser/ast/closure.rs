use crate::lexer::pos::{Position, Span};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::statement::Statement;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a closure, which is just a series of statements with their own scope.
#[derive(Debug, Clone)]
pub struct Closure {
    pub statements: Vec<Statement>,
    span: Span,
}

impl PartialEq for Closure {
    fn eq(&self, other: &Self) -> bool {
        self.statements == other.statements && self.span == other.span
    }
}

locatable_impl!(Closure);

impl Closure {
    /// Creates a new closure.
    pub fn new(statements: Vec<Statement>, span: Span) -> Self {
        Closure { statements, span }
    }

    /// Parses closures. Expects token sequences of the form
    ///
    ///     { <statement>; ... }
    ///
    /// where
    /// - `statement` is any valid statement
    /// - the semicolon is optional
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        // Record the closure starting position.
        let start_pos = parser.parse_expecting(TokenKind::LeftBrace)?.span.start_pos;
        let end_pos: Position;

        // The following nodes should be statements separated by an optional ";".
        let mut statements = vec![];
        loop {
            match parser.tokens.peek_next() {
                // If the next token is `}`, we've reached the end of the closure.
                Some(&Token {
                    kind: TokenKind::RightBrace,
                    ..
                }) => {
                    // We've reached the end of the closure. Move past `}` and break the loop.
                    let end_token = parser.tokens.next().unwrap();

                    // Record the closure ending position.
                    end_pos = end_token.span.end_pos;
                    break;
                }

                // If the next token is ";", we've reached the end of the statement.
                Some(&Token {
                    kind: TokenKind::SemiColon,
                    ..
                }) => {
                    parser.tokens.next();
                }

                // If the next token is anything else, we expect it to be the beginning of a new
                // statement.
                _ => {
                    let statement = Statement::parse(parser)?;
                    statements.push(statement);
                }
            };
        }

        Ok(Closure::new(
            statements,
            parser.new_span(start_pos, end_pos),
        ))
    }
}
