use lazy_static::lazy_static;
// use log::debug;
use regex::Regex;
use std::result::Result;

// Represents any valid token in the language.
#[derive(Debug)]
pub enum Token {
    Plus,
    Minus,
    Equal,
    Variable(String),
    Int(i64),
    Let,
    StringLiteral(String),
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
            _ => false,
        }
    }
}

impl Token {
    // Breaks the given slice into a list of tokens. If the slice contains any invalid tokens,
    // an error is returned.
    pub fn tokenize(segment: &str) -> Result<Vec<Token>, String> {
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
                return Err(format!("Expected valid token, but got \"{}\"", subseg));
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
        // Check +
        if let Some(v) = Token::parse_plus(segment) {
            return Some(v);
        }

        // Check -
        if let Some(v) = Token::parse_minus(segment) {
            return Some(v);
        }

        // Check =
        if let Some(v) = Token::parse_equal(segment) {
            return Some(v);
        }

        // Check let
        if let Some(v) = Token::parse_let(segment) {
            return Some(v);
        }

        // Check variable name
        if let Some(v) = Token::parse_variable(segment) {
            return Some(v);
        }

        // Check int
        if let Some(v) = Token::parse_int(segment) {
            return Some(v);
        }

        // Check string literal
        if let Some(v) = Token::parse_string_literal(segment) {
            return Some(v);
        }

        None
    }

    pub fn parse_plus(segment: &str) -> Option<Token> {
        match segment.trim() {
            "+" => Some(Token::Plus),
            _ => None,
        }
    }

    pub fn parse_minus(segment: &str) -> Option<Token> {
        match segment.trim() {
            "-" => Some(Token::Minus),
            _ => None,
        }
    }

    pub fn parse_let(segment: &str) -> Option<Token> {
        match segment.trim() {
            "let" => Some(Token::Let),
            _ => None,
        }
    }

    pub fn parse_int(segment: &str) -> Option<Token> {
        match segment.trim().parse::<i64>() {
            Ok(i) => Some(Token::Int(i)),
            Err(_) => None,
        }
    }

    pub fn parse_variable(segment: &str) -> Option<Token> {
        lazy_static! {
            static ref VARIABLE: Regex = Regex::new(r"^[a-zA-Z_]+[a-zA-Z0-9_]*$").unwrap();
        }
        match VARIABLE.is_match(segment.trim()) {
            true => Some(Token::Variable(String::from(segment.trim()))),
            false => None,
        }
    }

    pub fn parse_equal(segment: &str) -> Option<Token> {
        match segment.trim() {
            "=" => Some(Token::Equal),
            _ => None,
        }
    }

    pub fn parse_string_literal(segment: &str) -> Option<Token> {
        lazy_static! {
            static ref STRING_LITERAL: Regex = Regex::new(r#"^"(?:[^"\\]|\\.)*"$"#).unwrap();
        }
        match STRING_LITERAL.is_match(segment.trim()) {
            true => {
                // Trim leading and trailing whitespace.
                let formatted = segment.trim();

                // Removing opening and losing quotes
                let formatted = &formatted[1..formatted.len() - 1];

                // Change escaped quotes to just quotes and
                let formatted = &formatted.replace("\\\"", "\"").replace("\\\\", "\\");

                Some(Token::StringLiteral(String::from(formatted)))
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::token::Token;

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
    }
}
