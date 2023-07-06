use std::collections::VecDeque;
use std::fmt;
use std::io::{BufRead, Lines};

use crate::lexer::error::LexError;
use crate::lexer::kind::TokenKind;
use crate::lexer::pos::Position;
use crate::lexer::LexResult;

/// A token has a kind and a start and end position (in the file).
#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub start: Position,
    pub end: Position,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} to {}: {}", self.start, self.end, self.kind)
    }
}

impl Token {
    pub fn new(kind: TokenKind, line: usize, start_col: usize, end_col: usize) -> Self {
        Token {
            kind,
            start: Position::new(line, start_col),
            end: Position::new(line, end_col),
        }
    }

    /// Attempts to lex lines from the given reader and return a deque of tokens, or an error
    /// if the buffer contains invalid tokens.
    pub fn tokenize<B: BufRead>(lines: Lines<B>) -> LexResult<VecDeque<Token>> {
        let mut tokens = VecDeque::new();
        for (line_num, line) in lines.enumerate() {
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
            if let Some((kind, end_col)) = TokenKind::first_from(subseg) {
                // Ignore everything on the line after a comment.
                if kind == TokenKind::BeginComment {
                    break;
                }

                // The current subsegment begins with (or is entirely) a valid token. Store it and
                // record its end index so we can start the next search at the end of the current
                // token.
                let token_start = search_start + whitespace_prefix_size(subseg);
                let token_end = search_start + end_col - whitespace_suffix_size(&subseg[..end_col]);
                tokens.push_back(Token::new(kind, line_num, token_start, token_end));
                search_start += end_col;
            } else if subseg.trim().is_empty() {
                // The subsegment is just whitespace, so just continue from the end of the
                // subsegment.
                search_start += subseg.len();
            } else {
                // The subsegment does not begin with a valid token. This means the segment is
                // syntactically invalid.
                return Err(LexError::new(
                    format!(r#"Expected valid token, but found {}"#, subseg).as_str(),
                    line_num,
                    search_start,
                ));
            }
        }

        Ok(tokens)
    }
}

/// Returns the number of leading whitespace characters in the string.
fn whitespace_prefix_size(s: &str) -> usize {
    s.chars().take_while(|c| c.is_whitespace()).count()
}

/// Returns the number of trailing whitespace characters in the string.
fn whitespace_suffix_size(s: &str) -> usize {
    s.chars().rev().take_while(|c| c.is_whitespace()).count()
}
