use std::collections::VecDeque;
use std::fmt;
use std::fs::File;
use std::io::{BufRead, BufReader};

use crate::lexer::error::LexError;
use crate::lexer::kind::TokenKind;
use crate::lexer::pos::Position;
use crate::lexer::LexResult;

/// A token has a kind and a start and end position (in the file).
#[derive(Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub start: Position,
    pub end: Position,
}

impl Clone for Token {
    fn clone(&self) -> Self {
        Token {
            kind: self.kind.clone(),
            start: self.start,
            end: self.end,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} to {}: {}", self.start, self.end, self.kind)
    }
}

impl Token {
    pub fn new(kind: TokenKind, line: usize, start_col: usize) -> Self {
        let len = kind.len();
        Token {
            kind,
            start: Position::new(line, start_col),
            end: Position::new(line, start_col + len),
        }
    }

    /// Attempts to lex the file from the given reader and return a deque of tokens, or an error
    /// if the file contains invalid tokens.
    pub fn tokenize_file(reader: BufReader<File>) -> LexResult<VecDeque<Token>> {
        let mut tokens = VecDeque::new();
        for (line_num, line) in reader.lines().enumerate() {
            let line = match line {
                Ok(l) => l,
                Err(err) => {
                    return Err(LexError::new(
                        format!("Error reading line {}: {}", line_num, err).as_str(),
                        line_num,
                        0,
                    ))
                }
            };

            match Token::tokenize_line(line.as_str(), line_num) {
                Ok(tokens_from_line) => tokens.extend(tokens_from_line),
                Err(e) => return Err(e),
            };
        }

        Ok(tokens)
    }

    /// Breaks the given slice into a deque of tokens. If the slice contains any invalid tokens,
    /// an error is returned.
    pub fn tokenize_line(segment: &str, line_num: usize) -> LexResult<VecDeque<Token>> {
        let mut tokens = VecDeque::new();
        let mut search_start: usize = 0;

        while search_start < segment.len() {
            let subseg = &segment[search_start..];
            if let Some((kind, token_end)) = TokenKind::first_from(subseg) {
                // The current subsegment begins with (or is entirely) a valid token. Store it and
                // record its end index so we can start the next search at the end of the current
                // token.
                tokens.push_back(Token::new(kind, line_num, search_start));
                search_start += token_end;
            } else {
                // The subsegment does not begin with a valid token. This means the segment is
                // syntactically invalid.
                return Err(LexError::new(
                    format!(r#"Expected valid token, but got {}"#, subseg).as_str(),
                    line_num,
                    search_start,
                ));
            }
        }

        Ok(tokens)
    }
}
