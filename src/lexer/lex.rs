use colored::Colorize;
use flamer::flame;

use crate::lexer::error::{LexError, LexResult};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;

/// Lexes the given character stream into tokens.
#[flame]
pub fn lex(chars: &mut Stream<char>) -> LexResult<Vec<Token>> {
    let mut tokens = vec![];
    let mut line = 1;
    let mut col = 1;

    while chars.has_next() {
        // Advance the cursor in the stream until we find the next non-whitespace character.
        if !chars.seek(|c| {
            if !c.is_whitespace() {
                return true;
            }

            if c == &'\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }

            false
        }) {
            break;
        }

        // Save the current position in the stream as it marks the beginning of the next token.
        let token_start = chars.cursor();

        // Find the next whitespace region while also handling comments and string literals.
        let mut skip_comment = false;
        let mut block_comment_len = 0;
        let mut is_string_lit = false;
        let mut is_line_comment = false;
        let mut block_comment_depth = 0;
        let mut at_block_comment_end = false;
        let mut last_char = ' ';
        chars.seek(|c| {
            // Increment the block comment length counter if we're inside a block comment.
            if block_comment_depth > 0 {
                block_comment_len += 1;
            }

            // Return true to terminate the seek if we've found the end of the block comment.
            if at_block_comment_end {
                return true;
            }

            match c {
                // If we see an unescaped quote, and we're not in a comment, toggle the flag that
                // tells us whether we're in a string literal.
                '"' if last_char != '\\' && !is_line_comment && block_comment_depth == 0 => {
                    is_string_lit = !is_string_lit;
                }

                // If we see the start of a new block comment, and we're not in a string literal,
                // increment the block comment counter. Block comments can be nested like this:
                // `/* outer /* inner */ other */`.
                '*' if last_char == '/' && !is_string_lit && !is_line_comment => {
                    block_comment_depth += 1;

                    // Start the block comment length counter at 2 if this is the beginning
                    // of the first block comment. This is because the token that marks
                    // the beginning of block comments (`/*`) is 2 chars long.
                    if block_comment_depth == 1 {
                        block_comment_len = 2;
                    }
                }

                // If we see the end of a block comment, and we're not in a string literal, decrement
                // the block comment counter.
                '/' if last_char == '*'
                    && !is_string_lit
                    && !is_line_comment
                    && block_comment_depth > 0 =>
                {
                    block_comment_depth -= 1;

                    // Terminate on the next iteration if we've reached the end out the outermost
                    // block comment.
                    at_block_comment_end = block_comment_depth == 0;
                }

                // If we see the start of a line comment, and we're not in a comment or string
                // literal, toggle the flag that indicates we're in a line comment.
                '/' if last_char == '/' && !is_string_lit && block_comment_depth == 0 => {
                    skip_comment = true;
                    is_line_comment = true;
                }

                // Newlines should increment the line counter and reset the column counter, and
                // they should also mark the end of line comments.
                '\n' => {
                    if block_comment_depth == 0 && !is_string_lit {
                        return true;
                    }

                    line += 1;
                    col = 0;
                }

                _ => {
                    // Stop searching only if we're not in a string literal or comment, and we
                    // encounter whitespace.
                    if c.is_whitespace()
                        && block_comment_depth == 0
                        && !is_line_comment
                        && !is_string_lit
                    {
                        return true;
                    }
                }
            };

            last_char = *c;
            col += 1;
            false
        });

        if skip_comment {
            continue;
        }

        // Get a slice of the characters between the token start and the current cursor
        // position.
        let segment = chars.slice(token_start, chars.cursor() - block_comment_len);
        if !segment.is_empty() {
            match get_tokens(segment, line, col - segment.len()) {
                Ok(segment_tokens) => tokens.extend(segment_tokens),
                Err(err) => return Err(err),
            };
        }
    }

    Ok(tokens)
}

/// Splits the given segment into tokens and returns them. Returns an error if the segment was
/// not composed exclusively of valid tokens (without any whitespace).
fn get_tokens(segment: &[char], line: usize, col: usize) -> LexResult<Vec<Token>> {
    let mut tokens = vec![];

    for end_pos in (1..=segment.len()).rev() {
        let segment_left = String::from_iter(&segment[..end_pos]);
        match TokenKind::from(segment_left.as_str()) {
            Ok(Some(left_token_kind)) => {
                tokens.push(Token::new(left_token_kind, line, col, col + end_pos));

                if end_pos <= segment.len() - 1 {
                    match get_tokens(&segment[end_pos..], line, col + end_pos) {
                        Ok(right_tokens) => tokens.extend(right_tokens),
                        Err(err) => {
                            return Err(err);
                        }
                    }
                }

                return Ok(tokens);
            }

            Ok(None) => {}

            Err(msg) => {
                return Err(LexError::new(
                    format!(
                        "{}: {}",
                        format_code!("invalid token {}", String::from_iter(segment)),
                        msg
                    )
                    .as_str(),
                    line,
                    col,
                ))
            }
        }
    }

    Err(LexError::new(
        format!("invalid token {}", String::from_iter(segment)).as_str(),
        line,
        col,
    ))
}
