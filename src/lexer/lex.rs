
use flamer::flame;
use logos::{Logos};

use crate::lexer::error::{LexError, LexResult};

use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;


/// Lexes the given source code and returns a vec of tokens or an error if
/// the code contains invalid tokens.
#[flame]
pub fn lex(source_code: &str) -> LexResult<Vec<Token>> {
    let mut lexer = TokenKind::lexer(source_code);
    let mut tokens = vec![];
    let mut line_num = 1;
    let mut last_newline_offset = 0;

    while let Some(result) = lexer.next() {
        match result {
            Ok(kind) => match kind {
                // Track line count and skip newline characters.
                TokenKind::Newline(new_line_num) => {
                    line_num = new_line_num;
                    last_newline_offset = lexer.span().end;
                    continue;
                }

                // Skip comments.
                TokenKind::LineComment | TokenKind::BlockComment => {}

                _ => {
                    tokens.push(Token::new(
                        kind,
                        line_num,
                        lexer.span().start - last_newline_offset + 1,
                        lexer.span().end - last_newline_offset + 1,
                    ));
                }
            },
            Err(_) => {
                return Err(LexError::new(
                    "invalid token",
                    line_num,
                    lexer.span().start - last_newline_offset + 1,
                    lexer.span().end - last_newline_offset + 1,
                ))
            }
        }
    }

    Ok(tokens)
}
