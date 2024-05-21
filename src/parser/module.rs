use crate::fmt;
use crate::lexer::pos::Position;
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::r#use::UsedModule;
use crate::parser::ast::statement::Statement;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};

/// Represents a parsed source file.
#[derive(Debug)]
pub struct Module {
    pub path: String,
    pub used_mods: Vec<UsedModule>,
    pub statements: Vec<Statement>,
}

impl PartialEq for Module {
    fn eq(&self, other: &Self) -> bool {
        self.statements == other.statements && self.used_mods == other.used_mods
    }
}

impl Module {
    /// Attempts to parse a list of statements from the deque of tokens. Expects token sequences of
    /// the form
    ///
    ///     <statement>
    ///     ...
    ///
    /// where
    ///  - `statement` is a valid statement (see `Statement::from`)
    pub fn from(path: &str, tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let mut statements = vec![];
        let mut used_mods = vec![];
        while tokens.has_next() {
            match Statement::from(tokens) {
                Ok(statement) => match statement {
                    Statement::Use(used_mod) => {
                        used_mods.push(used_mod);
                    }
                    other => statements.push(other),
                },
                Err(err) => return Err(err),
            };
        }

        Ok(Module {
            path: path.to_string(),
            used_mods,
            statements,
        })
    }

    /// Returns an error if the next token is the given kind, or the token otherwise.
    pub fn parse_expecting(tokens: &mut Stream<Token>, expected: TokenKind) -> ParseResult<Token> {
        match tokens.next() {
            None => {
                return Err(ParseError::new(
                    ErrorKind::UnexpectedEOF,
                    format_code!(r#"expected {}, but found EOF"#, expected).as_str(),
                    None,
                    Position::default(),
                    Position::default(),
                ))
            }
            Some(token) => {
                if token.kind == expected {
                    Ok(token.clone())
                } else {
                    Err(ParseError::new_with_token(
                        ErrorKind::UnexpectedToken,
                        format_code!(r#"expected {}, but found {}"#, expected, token).as_str(),
                        token.clone(),
                    ))
                }
            }
        }
    }

    /// Returns an error if the next token is not any of the given kinds, or the token otherwise.
    pub fn parse_expecting_any(
        tokens: &mut Stream<Token>,
        expected: Vec<TokenKind>,
    ) -> ParseResult<Token> {
        match tokens.next() {
            None => {
                return Err(ParseError::new(
                    ErrorKind::UnexpectedEOF,
                    format!(
                        r#"expected {}{}, but found EOF"#,
                        if expected.len() > 1 { "one of " } else { "" },
                        fmt::format_code_vec(&expected, ", ")
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
                            r#"expected {}{}, but found {}"#,
                            if expected.len() > 1 { "one of " } else { "" },
                            fmt::format_code_vec(&expected, ", "),
                            format_code!("{}", token),
                        )
                        .as_str(),
                        token.clone(),
                    ))
                }
            }
        }
    }

    /// Returns true if the next token in the stream has the given kind.
    pub fn next_token_is(tokens: &Stream<Token>, kind: &TokenKind) -> bool {
        if let Some(token) = tokens.peek_next() {
            return &token.kind == kind;
        }

        false
    }

    /// Returns true if the next token is one of the given kinds.
    pub fn next_token_is_one_of(tokens: &Stream<Token>, kinds: &Vec<TokenKind>) -> bool {
        if let Some(token) = tokens.peek_next() {
            for kind in kinds {
                if &token.kind == kind {
                    return true;
                }
            }
        }

        false
    }

    /// Checks if the first token is the given kind and, if so, pops the token and returns
    /// it.
    pub fn parse_optional(tokens: &mut Stream<Token>, expected: TokenKind) -> Option<&Token> {
        if let Some(Token { kind, .. }) = tokens.peek_next() {
            if kind == &expected {
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
                    format_code!("expected identifier, but found {}", other).as_str(),
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

    /// Returns the end position of the previous token in the stream.
    pub fn prev_position(tokens: &Stream<Token>) -> Position {
        match tokens.prev() {
            Some(Token { kind: _, end, .. }) => Position {
                line: end.line,
                col: end.col,
            },
            None => Position::new(0, 0),
        }
    }
}
