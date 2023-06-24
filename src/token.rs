use lazy_static::lazy_static;
use regex::Regex;
use std::result::Result;

#[derive(Debug, PartialEq)]
pub struct ParseError {
    pub message: String,
    pub column: usize,
}

impl ParseError {
    fn new(message: &str, column: usize) -> Self {
        ParseError {
            message: message.to_string(),
            column,
        }
    }
}

// Represents any valid token in the language.
#[derive(Debug)]
pub enum Token {
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

    // Primitive types
    Int(i64),
    StringLiteral(String),

    // Keywords and control flow
    Let,
    If,
    Else,
    ElseIf,
    BeginClosure,
    EndClosure,

    // User-defined values
    Variable(String),
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        match (&self, other) {
            (Token::Plus, Token::Plus) => true,
            (Token::Minus, Token::Minus) => true,
            (Token::Let, Token::Let) => true,
            (Token::Equal, Token::Equal) => true,
            (Token::Variable(v1), Token::Variable(v2)) => v1 == v2,
            (Token::StringLiteral(v1), Token::StringLiteral(v2)) => v1 == v2,
            (Token::Int(v1), Token::Int(v2)) => v1 == v2,
            (Token::Equals, Token::Equals) => true,
            (Token::GreaterThan, Token::GreaterThan) => true,
            (Token::LessThan, Token::LessThan) => true,
            (Token::If, Token::If) => true,
            (Token::Else, Token::Else) => true,
            (Token::ElseIf, Token::ElseIf) => true,
            (Token::BeginClosure, Token::BeginClosure) => true,
            (Token::EndClosure, Token::EndClosure) => true,
            _ => false,
        }
    }
}

impl Token {
    // Breaks the given slice into a list of tokens. If the slice contains any invalid tokens,
    // an error is returned.
    pub fn tokenize(segment: &str) -> Result<Vec<Token>, ParseError> {
        let mut tokens = vec![];
        let mut search_start: usize = 0;

        while search_start < segment.len() {
            let subseg = &segment[search_start..];
            if let Some((token, token_end)) = Token::parse_first(subseg) {
                // The current subsegment begins with (or is entirely) a valid token. Store it and
                // record its end index so we can start the next search at the end of the current
                // token.
                tokens.push(token);
                search_start += token_end;
            } else {
                // The subsegment does not begin with a valid token. This means the segment is
                // syntactically invalid.
                return Err(ParseError::new(
                    format!(r#"Expected valid token, but got {}"#, subseg).as_str(),
                    search_start,
                ));
            }
        }

        Ok(tokens)
    }

    // Finds the first valid token in the slice and the index in the slice at which the token ends.
    // If the slice does not begin with a valid token, None will be returned.
    pub fn parse_first(segment: &str) -> Option<(Token, usize)> {
        let mut result = None;
        for token_end in 1..=segment.char_indices().count() {
            if let Some(token) = Token::parse(&segment[..token_end]) {
                // The current subsegment is a valid token.
                let greedy = token.is_greedy();
                result = Some((token, token_end));

                // If the current token is greedy, we should return it immediately.
                if greedy {
                    return result;
                }
            }
        }

        result
    }

    // Returns false if the token, when parsed, could possibly be a part of a larger token and true
    // otherwise.
    fn is_greedy(&self) -> bool {
        match self {
            Token::Plus | Token::Minus => true,
            _ => false,
        }
    }

    // Attempts to parse the given slice into a token. Returns None if the slice is not a valid
    // token.
    pub fn parse(segment: &str) -> Option<Token> {
        if let Some(v) = Token::parse_basic(segment, "+", Token::Plus) {
            return Some(v);
        }

        if let Some(v) = Token::parse_basic(segment, "-", Token::Minus) {
            return Some(v);
        }

        if let Some(v) = Token::parse_basic(segment, "=", Token::Equal) {
            return Some(v);
        }

        if let Some(v) = Token::parse_basic(segment, "let", Token::Let) {
            return Some(v);
        }

        if let Some(v) = Token::parse_int(segment) {
            return Some(v);
        }

        if let Some(v) = Token::parse_string_literal(segment) {
            return Some(v);
        }

        if let Some(v) = Token::parse_basic(segment, "==", Token::Equals) {
            return Some(v);
        }

        if let Some(v) = Token::parse_basic(segment, ">", Token::GreaterThan) {
            return Some(v);
        }

        if let Some(v) = Token::parse_basic(segment, "<", Token::LessThan) {
            return Some(v);
        }

        if let Some(v) = Token::parse_basic(segment, ">=", Token::GreaterThanOrEqual) {
            return Some(v);
        }

        if let Some(v) = Token::parse_basic(segment, "<=", Token::LessThanOrEqual) {
            return Some(v);
        }

        if let Some(v) = Token::parse_basic(segment, "if", Token::If) {
            return Some(v);
        }

        if let Some(v) = Token::parse_basic(segment, "else", Token::Else) {
            return Some(v);
        }

        let re_else_if = Regex::new(r#"^else\s*if$"#).unwrap();
        if let Some(v) = Token::parse_regex(segment, re_else_if, Token::ElseIf) {
            return Some(v);
        }

        if let Some(v) = Token::parse_basic(segment, "{", Token::BeginClosure) {
            return Some(v);
        }

        if let Some(v) = Token::parse_basic(segment, "}", Token::EndClosure) {
            return Some(v);
        }

        if let Some(v) = Token::parse_variable(segment) {
            return Some(v);
        }

        None
    }

    fn parse_basic(segment: &str, target: &str, token: Token) -> Option<Token> {
        if segment.trim() == target {
            return Some(token);
        }
        None
    }

    fn parse_regex(segment: &str, re: Regex, token: Token) -> Option<Token> {
        match re.is_match(segment.trim()) {
            true => Some(token),
            false => None,
        }
    }

    fn parse_int(segment: &str) -> Option<Token> {
        match segment.trim().parse::<i64>() {
            Ok(i) => Some(Token::Int(i)),
            Err(_) => None,
        }
    }

    fn parse_variable(segment: &str) -> Option<Token> {
        lazy_static! {
            static ref RE_VARIABLE: Regex = Regex::new(r"^[a-zA-Z_]+[a-zA-Z0-9_]*$").unwrap();
        }
        match RE_VARIABLE.is_match(segment.trim()) {
            true => Some(Token::Variable(String::from(segment.trim()))),
            false => None,
        }
    }

    fn parse_string_literal(segment: &str) -> Option<Token> {
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

                Some(Token::StringLiteral(String::from(formatted)))
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::token::{ParseError, Token};

    #[test]
    fn parse_let() {
        let result = Token::parse(" let ");
        assert_eq!(result, Some(Token::Let));

        let result = Token::parse(" ??a2 ");
        assert_eq!(result, None);
    }

    #[test]
    fn parse_plus() {
        let result = Token::parse(" + ");
        assert_eq!(result, Some(Token::Plus));

        let result = Token::parse(" aos83;2/ ");
        assert_eq!(result, None);
    }

    #[test]
    fn parse_minus() {
        let result = Token::parse(" - ");
        assert_eq!(result, Some(Token::Minus));

        let result = Token::parse(" ao9u5424lm/ ");
        assert_eq!(result, None);
    }

    #[test]
    fn parse_equal() {
        let result = Token::parse(" = ");
        assert_eq!(result, Some(Token::Equal));

        let result = Token::parse(" ?#li4kU#@(U* ");
        assert_eq!(result, None);
    }

    #[test]
    fn parse_int() {
        let result = Token::parse(" 123 ");
        assert_eq!(result, Some(Token::Int(123)));

        let result = Token::parse(" 9923423 ");
        assert_eq!(result, Some(Token::Int(9923423)));

        let result = Token::parse(" ..23423;lj1 ");
        assert_eq!(result, None);
    }

    #[test]
    fn parse_variable() {
        let result = Token::parse(" _a_2_32sdfkeFDSwre980 ");
        assert_eq!(
            result,
            Some(Token::Variable(String::from("_a_2_32sdfkeFDSwre980")))
        );

        let result = Token::parse(" asr32/23 ");
        assert_eq!(result, None);
    }

    #[test]
    fn parse_string_literal() {
        let result = Token::parse(" \"asdf\" ");
        assert_eq!(result, Some(Token::StringLiteral(String::from("asdf"))));

        let result = Token::parse(r#" "say \"something\"!!" "#);
        assert_eq!(
            result,
            Some(Token::StringLiteral(String::from(r#"say "something"!!"#)))
        );

        let result = Token::parse(r#" "" "#);
        assert_eq!(result, Some(Token::StringLiteral(String::from(""))));

        let result = Token::parse(r#" "\\\\" "#);
        assert_eq!(result, Some(Token::StringLiteral(String::from(r#"\\"#))));

        let result = Token::parse(r#" "23424?? "#);
        assert_eq!(result, None);
    }

    #[test]
    fn parse_first() {
        let result = Token::parse_first(" let thing  =1  ");
        assert_eq!(result, Some((Token::Let, 5)),);

        let result = Token::parse_first("letter ");
        assert_eq!(result, Some((Token::Variable(String::from("letter")), 7)),);

        let result = Token::parse_first("let thing 234 ");
        assert_eq!(result, Some((Token::Let, 4)));

        let result = Token::parse_first("thing 234 ");
        assert_eq!(result, Some((Token::Variable(String::from("thing")), 6)));

        let result = Token::parse_first("    3784751 --");
        assert_eq!(result, Some((Token::Int(3784751), 12)),);

        let result = Token::parse_first("  =letting 435");
        assert_eq!(result, Some((Token::Equal, 3)),);

        let result = Token::parse_first("  =letting ");
        assert_eq!(result, Some((Token::Equal, 3)),);

        let result = Token::parse_first("  +++++ ");
        assert_eq!(result, Some((Token::Plus, 3)),);

        let result = Token::parse_first("  -3480 ");
        assert_eq!(result, Some((Token::Minus, 3)),);

        let result = Token::parse_first(r#"  "some \"BIG\" string" "#);
        assert_eq!(
            result,
            Some((
                Token::StringLiteral(String::from(r#"some "BIG" string"#)),
                24,
            )),
        );

        let result = Token::parse_first(" :O#$J@#?@ ");
        assert_eq!(result, None);
    }

    #[test]
    fn tokenize() {
        let result = Token::tokenize(r#"let thing = 234 "onetwo" "three"four"" "\\\\\\""#);
        assert_eq!(
            result,
            Ok(vec![
                Token::Let,
                Token::Variable(String::from("thing")),
                Token::Equal,
                Token::Int(234),
                Token::StringLiteral(String::from("onetwo")),
                Token::StringLiteral(String::from("three")),
                Token::Variable(String::from("four")),
                Token::StringLiteral(String::from("")),
                Token::StringLiteral(String::from(r#"\\\"#)),
            ]),
        );

        let result = Token::tokenize(r#"if {} else if {} else {} elser iff"#);
        assert_eq!(
            result,
            Ok(vec![
                Token::If,
                Token::BeginClosure,
                Token::EndClosure,
                Token::ElseIf,
                Token::BeginClosure,
                Token::EndClosure,
                Token::Else,
                Token::BeginClosure,
                Token::EndClosure,
                Token::Variable(String::from("elser")),
                Token::Variable(String::from("iff")),
            ]),
        );

        let result = Token::tokenize(r#"<?>"#);
        if let Err(ParseError {
            message: _,
            column: col,
        }) = result
        {
            assert_eq!(col, 1);
        } else {
            panic!("Expected ParseErr");
        }
    }
}
