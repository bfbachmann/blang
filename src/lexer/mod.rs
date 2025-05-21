//! The Blang lexer is responsible for breaking raw source code into tokens that are meaningful
//! to the Blang parser.

pub mod error;
pub mod pos;
pub mod stream;
pub mod token;
pub mod token_kind;

use flamer::flame;
use logos::Logos;

use crate::lexer::error::{LexError, LexResult};
use crate::lexer::pos::{Position, Span};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::FileID;

/// Lexes the given source code and returns a vec of tokens or an error if
/// the code contains invalid tokens.
#[flame]
pub fn lex(source_code: &str, file_id: FileID) -> LexResult<Vec<Token>> {
    let mut lexer = TokenKind::lexer(source_code);
    let mut tokens = vec![];
    let mut last_token_end_line = 1;
    let mut previous_newline_offset = 0;
    let mut saw_newline = false;

    while let Some(result) = lexer.next() {
        let mut span = lexer.span();

        // If this is the first line in the source code, we need to increment
        // the offsets in the span because they start at 0, but we want to
        // start at 1.
        let is_first_line = previous_newline_offset == 0 && !saw_newline;
        if is_first_line {
            span.start += 1;
            span.end += 1;
        }

        let is_multiline_str_lit = match &result {
            Ok(TokenKind::StrLiteral(s)) => s.contains('\n'),
            _ => false,
        };

        // Calculate the start and end line and column numbers of the token.
        let token_start_line = last_token_end_line;
        let token_end_line = lexer.extras.0 as u32 + 1;
        let last_newline_offset = lexer.extras.1 as u32;
        let token_start_offset = span.start as u32;
        let token_end_offset = span.end as u32;
        let token_start_col = token_start_offset - previous_newline_offset;

        // Handle the special case where the code begins with a multiline `str`
        // literal.
        let token_end_col = match is_first_line && is_multiline_str_lit {
            true => token_end_offset - last_newline_offset - 2,
            false => token_end_offset - last_newline_offset,
        };

        previous_newline_offset = last_newline_offset;
        last_token_end_line = token_end_line;

        let token_start = Position::new(token_start_line, token_start_col);
        let token_end = Position::new(token_end_line, token_end_col);

        match result {
            Ok(kind) => match kind {
                // Skip comments.
                TokenKind::LineComment | TokenKind::BlockComment => {}

                // Set a flag to indicate that we've seen at least one newline.
                // This is to hand an edge case where the file starts with a
                // newline.
                TokenKind::Newline => {
                    saw_newline = true;
                }

                _ => {
                    tokens.push(Token {
                        kind,
                        span: Span {
                            file_id,
                            start_pos: token_start,
                            end_pos: token_end,
                        },
                    });
                }
            },

            Err(e) => {
                return Err(LexError {
                    message: format!("{} {}", e, format_code!(lexer.slice())),
                    span: Span {
                        file_id,
                        start_pos: token_start,
                        end_pos: Default::default(),
                    },
                })
            }
        }
    }

    Ok(tokens)
}
