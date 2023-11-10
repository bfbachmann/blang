use std::fmt;
use std::io::{BufRead, Lines};

use colored::Colorize;

use crate::lexer::error::LexError;
use crate::lexer::error::LexResult;
use crate::lexer::pos::Position;
use crate::lexer::token_kind::TokenKind;

/// A token has a kind and a start and end position (in the file).
#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub start: Position,
    pub end: Position,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.kind)
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
    pub fn tokenize<B: BufRead>(lines: Lines<B>) -> LexResult<Vec<Token>> {
        let mut tokens = vec![];
        for (line_num, line) in lines.enumerate() {
            // Line numbers should start from 1.
            let line_num = line_num + 1;

            let line = match line {
                Ok(l) => l,
                Err(err) => {
                    return Err(LexError::new(
                        format!("error reading line {}: {}", line_num, err).as_str(),
                        line_num,
                        1,
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
    pub fn tokenize_line(segment: &str, line_num: usize) -> LexResult<Vec<Token>> {
        let chars: Vec<char> = segment.chars().collect();
        let mut tokens = vec![];
        let mut search_start: usize = 0;

        while search_start < chars.len() {
            let subseg_chars = &chars[search_start..];
            let subseg = subseg_chars.iter().cloned().collect::<String>();
            let subseg = subseg.as_str();

            if let Some((kind, end_col)) = TokenKind::first_from(subseg) {
                // Ignore everything on the line after a comment.
                if kind == TokenKind::LineComment {
                    break;
                }

                // The current subsegment begins with (or is entirely) a valid token. Store it and
                // record its end index so we can start the next search at the end of the current
                // token. Note that indexes for line and column numbers start from 1.
                let token_start = search_start + whitespace_prefix_size(subseg) + 1;
                let token = subseg_chars[..end_col].iter().cloned().collect::<String>();
                let token_end = search_start + end_col - whitespace_suffix_size(token.as_str()) + 1;

                tokens.push(Token::new(kind, line_num, token_start, token_end));
                search_start += end_col;
            } else if subseg.trim().is_empty() {
                // The subsegment is just whitespace, so just continue from the end of the
                // subsegment.
                search_start += subseg.len();
            } else {
                // The subsegment does not begin with a valid token. This means the segment is
                // syntactically invalid.
                return Err(LexError::new(
                    format_code!("invalid token {}", subseg).as_str(),
                    line_num,
                    search_start + 1,
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
