use std::collections::{HashSet, VecDeque};

use crate::lexer::kind::TokenKind;
use crate::lexer::token::Token;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::statement::Statement;
use crate::parser::ParseResult;
use crate::util;

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
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        let mut statements = vec![];
        while !tokens.is_empty() {
            match Statement::from(tokens) {
                Ok(statement) => statements.push(statement),
                Err(err) => return Err(err),
            };
        }

        Ok(Program { statements })
    }

    /// Returns an error if the next token is not any of the given kinds, or the kind otherwise.
    pub fn parse_expecting(
        tokens: &mut VecDeque<Token>,
        expected: HashSet<TokenKind>,
    ) -> ParseResult<TokenKind> {
        match tokens.pop_front() {
            None => {
                return Err(ParseError::new(
                    ErrorKind::UnexpectedToken,
                    format!(r#"expected one of {:#?}"#, expected).as_str(),
                    None,
                ))
            }
            Some(token) => {
                if expected.contains(&token.kind) {
                    Ok(token.kind)
                } else {
                    Err(ParseError::new(
                        ErrorKind::UnexpectedToken,
                        format!(r#"expected one of {:#?}, but found "{}"#, expected, token)
                            .as_str(),
                        Some(token),
                    ))
                }
            }
        }
    }

    /// Checks if the first token is one of the given kinds and, if so, pops the token and returns
    /// it.
    pub fn parse_optional(
        tokens: &mut VecDeque<Token>,
        expected: HashSet<TokenKind>,
    ) -> Option<Token> {
        if let Some(Token { kind, .. }) = tokens.front() {
            let found_kind = expected.get(kind);
            if found_kind.is_some() {
                return tokens.pop_front();
            }
        }

        None
    }

    /// Parses an identifier, returning its name.
    pub fn parse_identifier(tokens: &mut VecDeque<Token>) -> ParseResult<String> {
        match tokens.pop_front() {
            Some(Token {
                kind: TokenKind::Identifier(name),
                ..
            }) => Ok(name),
            None => {
                return Err(ParseError::new(
                    ErrorKind::ExpectedIndent,
                    "expected identifier",
                    None,
                ))
            }
            Some(other) => {
                return Err(ParseError::new(
                    ErrorKind::ExpectedIndent,
                    format!(r#"expected identifier, but found "{}""#, other).as_str(),
                    Some(other),
                ))
            }
        }
    }
}
