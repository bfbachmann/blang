use crate::token_kind::TokenKind;
use std::collections::VecDeque;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::result::Result;

type LexResult<T> = Result<T, LexError>;

#[derive(Debug, PartialEq)]
pub struct LexError {
    message: String,
    line: usize,
    col: usize,
}

impl Error for LexError {}

impl LexError {
    fn new(message: &str, line: usize, col: usize) -> Self {
        LexError {
            message: message.to_string(),
            line,
            col,
        }
    }
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Lex error at position [{}:{}]: {}.",
            self.line, self.col, self.message
        )
    }
}

#[derive(Debug, PartialEq)]
pub struct Position {
    line: usize,
    col: usize,
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[{}:{}]", self.line, self.col)
    }
}

impl Position {
    fn new(line: usize, col: usize) -> Self {
        Position { line, col }
    }
}

/// A token has a kind and a start and end position (in the file).
#[derive(Debug, PartialEq)]
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
    fn new(kind: TokenKind, line: usize, start_col: usize) -> Self {
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

#[cfg(test)]
mod tests {
    use crate::lexer::{LexError, Token, TokenKind};
    use std::collections::VecDeque;

    #[test]
    fn lex_let() {
        let result = TokenKind::from(" let ");
        assert_eq!(result, Some(TokenKind::Let));

        let result = TokenKind::from(" ??a2 ");
        assert_eq!(result, None);
    }

    #[test]
    fn lex_add() {
        let result = TokenKind::from(" + ");
        assert_eq!(result, Some(TokenKind::Add));

        let result = TokenKind::from(" aos83;2/ ");
        assert_eq!(result, None);
    }

    #[test]
    fn lex_subtract() {
        let result = TokenKind::from(" - ");
        assert_eq!(result, Some(TokenKind::Subtract));

        let result = TokenKind::from(" ao9u5424lm/ ");
        assert_eq!(result, None);
    }

    #[test]
    fn lex_equal() {
        let result = TokenKind::from(" = ");
        assert_eq!(result, Some(TokenKind::Equal));

        let result = TokenKind::from(" ?#li4kU#@(U* ");
        assert_eq!(result, None);
    }

    #[test]
    fn lex_int_literal() {
        let result = TokenKind::from(" 123 ");
        assert_eq!(result, Some(TokenKind::IntLiteral(123)));

        let result = TokenKind::from(" 9923423 ");
        assert_eq!(result, Some(TokenKind::IntLiteral(9923423)));

        let result = TokenKind::from(" ..23423;lj1 ");
        assert_eq!(result, None);
    }

    #[test]
    fn lex_identifier() {
        let result = TokenKind::from(" _a_2_32sdfkeFDSwre980 ");
        assert_eq!(
            result,
            Some(TokenKind::Identifier(String::from("_a_2_32sdfkeFDSwre980")))
        );

        let result = TokenKind::from(" asr32/23 ");
        assert_eq!(result, None);
    }

    #[test]
    fn lex_string_literal() {
        let result = TokenKind::from(" \"asdf\" ");
        assert_eq!(result, Some(TokenKind::StringLiteral(String::from("asdf"))));

        let result = TokenKind::from(r#" "say \"something\"!!" "#);
        assert_eq!(
            result,
            Some(TokenKind::StringLiteral(String::from(
                r#"say "something"!!"#
            )))
        );

        let result = TokenKind::from(r#" "" "#);
        assert_eq!(result, Some(TokenKind::StringLiteral(String::from(""))));

        let result = TokenKind::from(r#" "\\\\" "#);
        assert_eq!(
            result,
            Some(TokenKind::StringLiteral(String::from(r#"\\"#)))
        );

        let result = TokenKind::from(r#" "23424?? "#);
        assert_eq!(result, None);
    }

    #[test]
    fn lex_first() {
        let result = TokenKind::first_from(" let thing  =1  ");
        assert_eq!(result, Some((TokenKind::Let, 5)),);

        let result = TokenKind::first_from("letter ");
        assert_eq!(
            result,
            Some((TokenKind::Identifier(String::from("letter")), 7)),
        );

        let result = TokenKind::first_from("let thing 234 ");
        assert_eq!(result, Some((TokenKind::Let, 4)));

        let result = TokenKind::first_from("thing 234 ");
        assert_eq!(
            result,
            Some((TokenKind::Identifier(String::from("thing")), 6))
        );

        let result = TokenKind::first_from("    3784751 --");
        assert_eq!(result, Some((TokenKind::IntLiteral(3784751), 12)),);

        let result = TokenKind::first_from("  =letting 435");
        assert_eq!(result, Some((TokenKind::Equal, 3)),);

        let result = TokenKind::first_from("  =letting ");
        assert_eq!(result, Some((TokenKind::Equal, 3)),);

        let result = TokenKind::first_from("  +++++ ");
        assert_eq!(result, Some((TokenKind::Add, 3)),);

        let result = TokenKind::first_from("  -3480 ");
        assert_eq!(result, Some((TokenKind::Subtract, 3)),);

        let result = TokenKind::first_from(r#"  "some \"BIG\" string" "#);
        assert_eq!(
            result,
            Some((
                TokenKind::StringLiteral(String::from(r#"some "BIG" string"#)),
                24,
            )),
        );

        let result = TokenKind::first_from(" :O#$J@#?@ ");
        assert_eq!(result, None);
    }

    #[test]
    fn tokenize_line() {
        let result = Token::tokenize_line(r#"let thing = 234 "onetwo" "three"four"" "\\\\\\""#, 0);
        assert_eq!(
            result,
            Ok(VecDeque::from(vec![
                Token::new(TokenKind::Let, 0, 0),
                Token::new(TokenKind::Identifier(String::from("thing")), 0, 4),
                Token::new(TokenKind::Equal, 0, 10),
                Token::new(TokenKind::IntLiteral(234), 0, 12),
                Token::new(TokenKind::StringLiteral(String::from("onetwo")), 0, 16),
                Token::new(TokenKind::StringLiteral(String::from("three")), 0, 25),
                Token::new(TokenKind::Identifier(String::from("four")), 0, 32),
                Token::new(TokenKind::StringLiteral(String::from("")), 0, 36),
                Token::new(TokenKind::StringLiteral(String::from(r#"\\\"#)), 0, 39),
            ])),
        );

        let result = Token::tokenize_line(r#"if {} else if {} else {} elser iff"#, 100);
        assert_eq!(
            result,
            Ok(VecDeque::from(vec![
                Token::new(TokenKind::If, 100, 0),
                Token::new(TokenKind::BeginClosure, 100, 3),
                Token::new(TokenKind::EndClosure, 100, 4),
                Token::new(TokenKind::ElseIf, 100, 6),
                Token::new(TokenKind::BeginClosure, 100, 14),
                Token::new(TokenKind::EndClosure, 100, 15),
                Token::new(TokenKind::Else, 100, 17),
                Token::new(TokenKind::BeginClosure, 100, 22),
                Token::new(TokenKind::EndClosure, 100, 23),
                Token::new(TokenKind::Identifier(String::from("elser")), 100, 25),
                Token::new(TokenKind::Identifier(String::from("iff")), 100, 31),
            ])),
        );

        let result = Token::tokenize_line(r#"<?>"#, 0);
        if let Err(LexError {
            message: _,
            line: _,
            col,
        }) = result
        {
            assert_eq!(col, 1);
        } else {
            panic!("Expected TokenizeError");
        }
    }
}
