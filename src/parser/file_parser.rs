use crate::fmt;
use crate::lexer::pos::{Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::error::{ErrorKind, ParseError, ParseResult};
use crate::parser::FileID;

pub struct FileParser {
    pub file_id: FileID,
    pub tokens: Stream<Token>,
}

impl FileParser {
    pub fn new(file_id: FileID, tokens: Stream<Token>) -> FileParser {
        FileParser { file_id, tokens }
    }

    /// Returns an error if the next token is the given kind, or the token otherwise.
    pub fn parse_expecting(&mut self, expected: TokenKind) -> ParseResult<Token> {
        match self.tokens.next() {
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                format_code!(r#"expected {}, but found EOF"#, expected).as_str(),
                None,
                Default::default(),
            )),
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
    pub fn parse_expecting_any(&mut self, expected: Vec<TokenKind>) -> ParseResult<Token> {
        match self.tokens.next() {
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                format!(
                    r#"expected {}{}, but found EOF"#,
                    if expected.len() > 1 { "one of " } else { "" },
                    fmt::format_code_vec(&expected, ", ")
                )
                .as_str(),
                None,
                Default::default(),
            )),
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
    pub fn next_token_is(&self, kind: &TokenKind) -> bool {
        if let Some(token) = self.tokens.peek_next() {
            return &token.kind == kind;
        }

        false
    }

    /// Returns true if the next token is one of the given kinds.
    pub fn next_token_is_one_of(&self, kinds: &Vec<TokenKind>) -> bool {
        if let Some(token) = self.tokens.peek_next() {
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
    pub fn parse_optional(&mut self, expected: TokenKind) -> Option<&Token> {
        if let Some(Token { kind, .. }) = self.tokens.peek_next() {
            if kind == &expected {
                return self.tokens.next();
            }
        }

        None
    }

    /// Parses an identifier, returning its name.
    pub fn parse_identifier(&mut self) -> ParseResult<String> {
        match self.tokens.next() {
            Some(Token {
                kind: TokenKind::Identifier(name),
                ..
            }) => Ok(name.clone()),
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected identifier, but found EOF",
                None,
                Default::default(),
            )),
            Some(other) => Err(ParseError::new_with_token(
                ErrorKind::ExpectedIdent,
                format_code!("expected identifier, but found {}", other).as_str(),
                other.clone(),
            )),
        }
    }

    /// Returns the current position in the file based on the head of the token deque.
    pub fn current_position(&self) -> Position {
        match self.tokens.peek_next() {
            Some(Token { kind: _, span, .. }) => Position {
                line: span.start_pos.line,
                col: span.start_pos.col,
            },
            None => Position::new(0, 0),
        }
    }

    /// Returns the end position of the previous token in the stream.
    pub fn prev_position(&self) -> Position {
        match self.tokens.prev() {
            Some(Token { kind: _, span, .. }) => Position {
                line: span.end_pos.line,
                col: span.end_pos.col,
            },
            None => Position::new(0, 0),
        }
    }

    /// Returns a new span for the current file being parsed.
    pub fn new_span(&self, start_pos: Position, end_pos: Position) -> Span {
        Span {
            file_id: self.file_id,
            start_pos,
            end_pos,
        }
    }
}
