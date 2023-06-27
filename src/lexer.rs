use lazy_static::lazy_static;
use regex::Regex;
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

#[derive(Debug)]
pub struct Position {
    line: usize,
    col: usize,
}

impl PartialEq for Position {
    fn eq(&self, other: &Self) -> bool {
        self.line == other.line && self.col == other.col
    }
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

/// Represents any valid token in the language.
#[derive(Debug, Eq, Hash)]
pub enum TokenKind {
    // Binary mathematical operators
    Plus,
    Minus,

    // Variable assignment
    Equal,

    // Comparators
    Equals,
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,

    // Built-in/primitive types
    Int,
    IntLiteral(i64),
    String,
    StringLiteral(String),
    Function,

    // Keywords and control flow
    Let,
    If,
    Else,
    ElseIf,
    Loop,
    Break,

    // Delimiters
    BeginClosure,
    EndClosure,
    OpenParen,
    CloseParen,
    Comma,
    SemiColon,

    // User-defined values
    Identifier(String),
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::Equal => write!(f, "="),
            TokenKind::Equals => write!(f, "=="),
            TokenKind::GreaterThan => write!(f, ">"),
            TokenKind::LessThan => write!(f, "<"),
            TokenKind::GreaterThanOrEqual => write!(f, ">="),
            TokenKind::LessThanOrEqual => write!(f, "<="),
            TokenKind::IntLiteral(i) => write!(f, "{} (integer literal)", i.to_string()),
            TokenKind::String => write!(f, "type string"),
            TokenKind::StringLiteral(s) => write!(f, "{} (string literal)", s),
            TokenKind::Function => write!(f, "function declaration"),
            TokenKind::Let => write!(f, "let"),
            TokenKind::If => write!(f, "if"),
            TokenKind::Else => write!(f, "else"),
            TokenKind::ElseIf => write!(f, "else if"),
            TokenKind::Loop => write!(f, "loop"),
            TokenKind::BeginClosure => write!(f, "{{"),
            TokenKind::EndClosure => write!(f, "}}"),
            TokenKind::Identifier(s) => write!(f, "{} (identifier)", s),
            TokenKind::Int => write!(f, "type integer"),
            TokenKind::OpenParen => write!(f, "("),
            TokenKind::CloseParen => write!(f, ")"),
            TokenKind::Comma => write!(f, ","),
            TokenKind::SemiColon => write!(f, ";"),
            TokenKind::Break => write!(f, "break"),
        }
    }
}

impl PartialEq for TokenKind {
    fn eq(&self, other: &Self) -> bool {
        match (&self, other) {
            (TokenKind::Plus, TokenKind::Plus) => true,
            (TokenKind::Minus, TokenKind::Minus) => true,
            (TokenKind::Let, TokenKind::Let) => true,
            (TokenKind::Equal, TokenKind::Equal) => true,
            (TokenKind::Identifier(v1), TokenKind::Identifier(v2)) => v1 == v2,
            (TokenKind::StringLiteral(v1), TokenKind::StringLiteral(v2)) => v1 == v2,
            (TokenKind::IntLiteral(v1), TokenKind::IntLiteral(v2)) => v1 == v2,
            (TokenKind::Equals, TokenKind::Equals) => true,
            (TokenKind::GreaterThan, TokenKind::GreaterThan) => true,
            (TokenKind::LessThan, TokenKind::LessThan) => true,
            (TokenKind::GreaterThanOrEqual, TokenKind::GreaterThanOrEqual) => true,
            (TokenKind::LessThanOrEqual, TokenKind::LessThanOrEqual) => true,
            (TokenKind::If, TokenKind::If) => true,
            (TokenKind::Else, TokenKind::Else) => true,
            (TokenKind::ElseIf, TokenKind::ElseIf) => true,
            (TokenKind::BeginClosure, TokenKind::BeginClosure) => true,
            (TokenKind::EndClosure, TokenKind::EndClosure) => true,
            (TokenKind::String, TokenKind::String) => true,
            (TokenKind::Loop, TokenKind::Loop) => true,
            (TokenKind::Int, TokenKind::Int) => true,
            (TokenKind::OpenParen, TokenKind::OpenParen) => true,
            (TokenKind::CloseParen, TokenKind::CloseParen) => true,
            (TokenKind::Comma, TokenKind::Comma) => true,
            (TokenKind::SemiColon, TokenKind::SemiColon) => true,
            (TokenKind::Function, TokenKind::Function) => true,
            (TokenKind::Break, TokenKind::Break) => true,
            _ => false,
        }
    }
}

impl TokenKind {
    fn to_string(&self) -> String {
        match self {
            TokenKind::Plus => "+".to_string(),
            TokenKind::Minus => "-".to_string(),
            TokenKind::Equal => "=".to_string(),
            TokenKind::Equals => "==".to_string(),
            TokenKind::GreaterThan => ">".to_string(),
            TokenKind::LessThan => "<".to_string(),
            TokenKind::GreaterThanOrEqual => ">=".to_string(),
            TokenKind::LessThanOrEqual => "<=".to_string(),
            TokenKind::IntLiteral(v) => v.to_string(),
            TokenKind::String => "string".to_string(),
            TokenKind::StringLiteral(v) => v.to_string(),
            TokenKind::Function => "fn".to_string(),
            TokenKind::Let => "let".to_string(),
            TokenKind::If => "if".to_string(),
            TokenKind::Else => "else".to_string(),
            TokenKind::ElseIf => "else if".to_string(),
            TokenKind::Loop => "loop".to_string(),
            TokenKind::BeginClosure => "{{".to_string(),
            TokenKind::EndClosure => "}}".to_string(),
            TokenKind::Identifier(v) => v.to_string(),
            TokenKind::Int => "int".to_string(),
            TokenKind::OpenParen => "(".to_string(),
            TokenKind::CloseParen => ")".to_string(),
            TokenKind::Comma => ",".to_string(),
            TokenKind::SemiColon => ";".to_string(),
            TokenKind::Break => "break".to_string(),
        }
    }

    /// Returns false if the token, when lexed, could possibly be a part of a larger token and true
    /// otherwise.
    fn is_greedy(&self) -> bool {
        match self {
            TokenKind::Plus | TokenKind::Minus => true,
            _ => false,
        }
    }

    /// Returns the number of characters in the token.
    fn len(&self) -> usize {
        self.to_string().len()
    }

    /// Finds the first valid TokenKind in the slice and the index in the slice at which the token
    /// ends. If the slice does not begin with a valid token, None will be returned.
    fn first_from(segment: &str) -> Option<(TokenKind, usize)> {
        let mut result = None;
        for token_end in 1..=segment.char_indices().count() {
            if let Some(kind) = TokenKind::from(&segment[..token_end]) {
                // The current subsegment is a valid token.
                // If the current token is greedy, we should return it immediately.
                if kind.is_greedy() {
                    return Some((kind, token_end));
                }
                result = Some((kind, token_end));
            }
        }

        result
    }

    /// Attempts to lex the given slice into a TokenKind. Returns None if the slice is not a valid
    /// token.
    fn from(segment: &str) -> Option<TokenKind> {
        if let Some(v) = TokenKind::lex_basic(segment, "+", TokenKind::Plus) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "-", TokenKind::Minus) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "=", TokenKind::Equal) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "let", TokenKind::Let) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "int", TokenKind::Int) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "==", TokenKind::Equals) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, ">", TokenKind::GreaterThan) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "<", TokenKind::LessThan) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, ">=", TokenKind::GreaterThanOrEqual) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "<=", TokenKind::LessThanOrEqual) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "if", TokenKind::If) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "else", TokenKind::Else) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "string", TokenKind::String) {
            return Some(v);
        }

        let re_else_if = Regex::new(r#"^else\s*if$"#).unwrap();
        if let Some(v) = TokenKind::lex_regex(segment, re_else_if, TokenKind::ElseIf) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "{", TokenKind::BeginClosure) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "}", TokenKind::EndClosure) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "(", TokenKind::OpenParen) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, ")", TokenKind::CloseParen) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, ",", TokenKind::Comma) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, ";", TokenKind::SemiColon) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "fn", TokenKind::Function) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "loop", TokenKind::Loop) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_basic(segment, "break", TokenKind::Break) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_int_literal(segment) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_string_literal(segment) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_identifier(segment) {
            return Some(v);
        }

        None
    }

    fn lex_basic(segment: &str, target: &str, token: TokenKind) -> Option<TokenKind> {
        if segment.trim() == target {
            return Some(token);
        }
        None
    }

    fn lex_regex(segment: &str, re: Regex, token: TokenKind) -> Option<TokenKind> {
        match re.is_match(segment.trim()) {
            true => Some(token),
            false => None,
        }
    }

    fn lex_int_literal(segment: &str) -> Option<TokenKind> {
        match segment.trim().parse::<i64>() {
            Ok(i) => Some(TokenKind::IntLiteral(i)),
            Err(_) => None,
        }
    }

    fn lex_identifier(segment: &str) -> Option<TokenKind> {
        lazy_static! {
            static ref RE_IDENTIFIER: Regex = Regex::new(r"^[a-zA-Z_]+[a-zA-Z0-9_]*$").unwrap();
        }
        match RE_IDENTIFIER.is_match(segment.trim()) {
            true => Some(TokenKind::Identifier(String::from(segment.trim()))),
            false => None,
        }
    }

    fn lex_string_literal(segment: &str) -> Option<TokenKind> {
        lazy_static! {
            static ref RE_STRING_LITERAL: Regex = Regex::new(r#"^"(?:[^"\\]|\\.)*"$"#).unwrap();
        }
        match RE_STRING_LITERAL.is_match(segment.trim()) {
            true => {
                // Trim leading and trailing whitespace.
                let formatted = segment.trim();

                // Removing opening and losing quotes
                let formatted = &formatted[1..formatted.len() - 1];

                // Change escaped quotes to just quotes and
                let formatted = &formatted.replace(r#"\""#, r#"""#).replace(r#"\\"#, r#"\"#);

                Some(TokenKind::StringLiteral(String::from(formatted)))
            }
            false => None,
        }
    }
}

/// A token has a kind and a start and end position (in the file).
#[derive(Debug)]
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

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.start == other.start && self.end == other.end
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
        let mut tokens = VecDeque::from(vec![]);
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
        let mut tokens = VecDeque::from(vec![]);
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
    fn lex_plus() {
        let result = TokenKind::from(" + ");
        assert_eq!(result, Some(TokenKind::Plus));

        let result = TokenKind::from(" aos83;2/ ");
        assert_eq!(result, None);
    }

    #[test]
    fn lex_minus() {
        let result = TokenKind::from(" - ");
        assert_eq!(result, Some(TokenKind::Minus));

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
        assert_eq!(result, Some((TokenKind::Plus, 3)),);

        let result = TokenKind::first_from("  -3480 ");
        assert_eq!(result, Some((TokenKind::Minus, 3)),);

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
