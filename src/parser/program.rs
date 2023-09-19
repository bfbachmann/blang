use std::collections::HashSet;

use colored::Colorize;

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::Position;
use crate::lexer::token::Token;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::statement::Statement;
use crate::parser::stream::Stream;
use crate::{fmt, util};

/// Represents a complete and syntactically valid (but not necessarily semantically valid) program.
#[derive(Debug)]
pub struct Program {
    pub statements: Vec<Statement>,
}

impl PartialEq for Program {
    fn eq(&self, other: &Self) -> bool {
        util::vectors_are_equal(&self.statements, &other.statements)
    }
}

impl Program {
    /// Attempts to parse a program from the deque of tokens. Expects token sequences of the form
    ///
    ///     <statement>
    ///     ...
    ///
    /// where
    ///  - `statement` is a valid statement (see `Statement::from`)
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let mut statements = vec![];
        while tokens.has_next() {
            match Statement::from(tokens) {
                Ok(statement) => statements.push(statement),
                Err(err) => return Err(err),
            };
        }

        Ok(Program { statements })
    }

    /// Returns an error if the next token is not any of the given kinds, or the token otherwise.
    pub fn parse_expecting(
        tokens: &mut Stream<Token>,
        expected: HashSet<TokenKind>,
    ) -> ParseResult<Token> {
        match tokens.next() {
            None => {
                return Err(ParseError::new(
                    ErrorKind::UnexpectedEOF,
                    format!(
                        r#"expected one of {}, but found EOF"#,
                        fmt::format_hashset(expected)
                    )
                    .as_str(),
                    None,
                    Position::default(),
                    Position::default(),
                ))
            }
            Some(token) => {
                if expected.contains(&token.kind) {
                    Ok(token.clone())
                } else {
                    Err(ParseError::new_with_token(
                        ErrorKind::UnexpectedToken,
                        format!(
                            r#"expected one of {}, but found {}"#,
                            fmt::format_hashset(expected),
                            format_code!("{}", token),
                        )
                        .as_str(),
                        token.clone(),
                    ))
                }
            }
        }
    }

    /// Checks if the first token is one of the given kinds and, if so, pops the token and returns
    /// it.
    pub fn parse_optional(
        tokens: &mut Stream<Token>,
        expected: HashSet<TokenKind>,
    ) -> Option<&Token> {
        if let Some(Token { kind, .. }) = tokens.peek_next() {
            let found_kind = expected.get(&kind);
            if found_kind.is_some() {
                return tokens.next();
            }
        }

        None
    }

    /// Parses an identifier, returning its name.
    pub fn parse_identifier(tokens: &mut Stream<Token>) -> ParseResult<String> {
        match tokens.next() {
            Some(Token {
                kind: TokenKind::Identifier(name),
                ..
            }) => Ok(name.clone()),
            None => {
                return Err(ParseError::new(
                    ErrorKind::UnexpectedEOF,
                    "expected identifier, but found EOF",
                    None,
                    Position::default(),
                    Position::default(),
                ))
            }
            Some(other) => {
                return Err(ParseError::new_with_token(
                    ErrorKind::ExpectedIdent,
                    format!(r#"expected identifier, but found "{}""#, other).as_str(),
                    other.clone(),
                ))
            }
        }
    }

    /// Returns the current position in the file based on the head of the token deque.
    pub fn current_position(tokens: &Stream<Token>) -> Position {
        match tokens.peek_next() {
            Some(Token { kind: _, start, .. }) => Position {
                line: start.line,
                col: start.col,
            },
            None => Position::new(0, 0),
        }
    }
}
