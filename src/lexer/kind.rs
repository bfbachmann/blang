use std::fmt;

use lazy_static::lazy_static;
use regex::Regex;

/// Represents any valid token in the language.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum TokenKind {
    // Binary operators
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    LogicalAnd,
    LogicalOr,

    // Unary operators
    Not,

    // Variable assignment
    Equal,

    // Comparators
    EqualTo,
    NotEqualTo,
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,

    // Built-in/primitive types
    Bool,
    BoolLiteral(bool),
    I64,
    I64Literal(i64),
    String,
    StringLiteral(String),
    Function,

    // Keywords and control flow
    If,
    Else,
    ElseIf,
    Loop,
    Break,
    Return,

    // Delimiters
    BeginClosure,
    EndClosure,
    LeftParen,
    RightParen,
    Comma,
    SemiColon,
    Colon,
    BeginComment,

    // User-defined values
    Identifier(String),
}

impl Clone for TokenKind {
    fn clone(&self) -> Self {
        match self {
            TokenKind::Add => TokenKind::Add,
            TokenKind::Subtract => TokenKind::Subtract,
            TokenKind::Multiply => TokenKind::Multiply,
            TokenKind::Divide => TokenKind::Divide,
            TokenKind::Modulo => TokenKind::Modulo,
            TokenKind::LogicalAnd => TokenKind::LogicalAnd,
            TokenKind::LogicalOr => TokenKind::LogicalOr,
            TokenKind::Not => TokenKind::Not,
            TokenKind::Equal => TokenKind::Equal,
            TokenKind::EqualTo => TokenKind::EqualTo,
            TokenKind::NotEqualTo => TokenKind::NotEqualTo,
            TokenKind::GreaterThan => TokenKind::GreaterThan,
            TokenKind::LessThan => TokenKind::LessThan,
            TokenKind::GreaterThanOrEqual => TokenKind::GreaterThanOrEqual,
            TokenKind::LessThanOrEqual => TokenKind::LessThanOrEqual,
            TokenKind::Bool => TokenKind::Bool,
            TokenKind::BoolLiteral(v) => TokenKind::BoolLiteral(*v),
            TokenKind::I64 => TokenKind::I64,
            TokenKind::I64Literal(v) => TokenKind::I64Literal(*v),
            TokenKind::String => TokenKind::String,
            TokenKind::StringLiteral(v) => TokenKind::StringLiteral(v.clone()),
            TokenKind::Function => TokenKind::Function,
            TokenKind::If => TokenKind::If,
            TokenKind::Else => TokenKind::Else,
            TokenKind::ElseIf => TokenKind::ElseIf,
            TokenKind::Loop => TokenKind::Loop,
            TokenKind::Break => TokenKind::Break,
            TokenKind::Return => TokenKind::Return,
            TokenKind::BeginClosure => TokenKind::BeginClosure,
            TokenKind::EndClosure => TokenKind::EndClosure,
            TokenKind::LeftParen => TokenKind::LeftParen,
            TokenKind::RightParen => TokenKind::RightParen,
            TokenKind::Comma => TokenKind::Comma,
            TokenKind::SemiColon => TokenKind::SemiColon,
            TokenKind::Colon => TokenKind::Colon,
            TokenKind::BeginComment => TokenKind::BeginComment,
            TokenKind::Identifier(v) => TokenKind::Identifier(v.clone()),
        }
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TokenKind::BoolLiteral(b) => write!(f, "boolean literal {}", b.to_string()),
            TokenKind::I64Literal(i) => write!(f, "i64 literal {}", i.to_string()),
            TokenKind::StringLiteral(s) => write!(f, r#"string literal "{}""#, s),
            TokenKind::Identifier(s) => write!(f, r#"identifier "{}""#, s),
            other => write!(f, r#""{}""#, other.to_string()),
        }
    }
}

impl TokenKind {
    fn to_string(&self) -> String {
        match self {
            TokenKind::Add => "+".to_string(),
            TokenKind::Subtract => "-".to_string(),
            TokenKind::Multiply => "*".to_string(),
            TokenKind::Divide => "/".to_string(),
            TokenKind::Modulo => "%".to_string(),
            TokenKind::LogicalAnd => "&&".to_string(),
            TokenKind::LogicalOr => "||".to_string(),
            TokenKind::Not => "!".to_string(),
            TokenKind::Equal => "=".to_string(),
            TokenKind::EqualTo => "==".to_string(),
            TokenKind::NotEqualTo => "!=".to_string(),
            TokenKind::GreaterThan => ">".to_string(),
            TokenKind::LessThan => "<".to_string(),
            TokenKind::GreaterThanOrEqual => ">=".to_string(),
            TokenKind::LessThanOrEqual => "<=".to_string(),
            TokenKind::Bool => "bool".to_string(),
            TokenKind::BoolLiteral(v) => v.to_string(),
            TokenKind::I64Literal(v) => v.to_string(),
            TokenKind::String => "string".to_string(),
            TokenKind::StringLiteral(v) => v.to_string(),
            TokenKind::Function => "fn".to_string(),
            TokenKind::If => "if".to_string(),
            TokenKind::Else => "else".to_string(),
            TokenKind::ElseIf => "else if".to_string(),
            TokenKind::Loop => "loop".to_string(),
            TokenKind::BeginClosure => "{".to_string(),
            TokenKind::EndClosure => "}".to_string(),
            TokenKind::Identifier(v) => v.to_string(),
            TokenKind::I64 => "i64".to_string(),
            TokenKind::LeftParen => "(".to_string(),
            TokenKind::RightParen => ")".to_string(),
            TokenKind::Comma => ",".to_string(),
            TokenKind::SemiColon => ";".to_string(),
            TokenKind::Colon => ":".to_string(),
            TokenKind::Break => "break".to_string(),
            TokenKind::Return => "return".to_string(),
            TokenKind::BeginComment => "//".to_string(),
        }
    }

    /// Returns false if the token, when lexed, could possibly be a part of a larger token and true
    /// otherwise.
    fn is_greedy(&self) -> bool {
        match self {
            TokenKind::Add | TokenKind::Subtract => true,
            _ => false,
        }
    }

    /// Finds the first valid TokenKind in the slice and the index in the slice at which the token
    /// ends. If the slice does not begin with a valid token, None will be returned.
    pub fn first_from(segment: &str) -> Option<(TokenKind, usize)> {
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
    pub fn from(segment: &str) -> Option<TokenKind> {
        let basic_kinds = [
            TokenKind::Add,
            TokenKind::Subtract,
            TokenKind::Multiply,
            TokenKind::Divide,
            TokenKind::Modulo,
            TokenKind::LogicalAnd,
            TokenKind::LogicalOr,
            TokenKind::Not,
            TokenKind::Equal,
            TokenKind::I64,
            TokenKind::Bool,
            TokenKind::EqualTo,
            TokenKind::NotEqualTo,
            TokenKind::GreaterThan,
            TokenKind::LessThan,
            TokenKind::GreaterThanOrEqual,
            TokenKind::LessThanOrEqual,
            TokenKind::If,
            TokenKind::Else,
            TokenKind::String,
            TokenKind::BeginClosure,
            TokenKind::EndClosure,
            TokenKind::LeftParen,
            TokenKind::RightParen,
            TokenKind::Comma,
            TokenKind::SemiColon,
            TokenKind::Colon,
            TokenKind::Function,
            TokenKind::Loop,
            TokenKind::Break,
            TokenKind::Return,
            TokenKind::BeginComment,
        ];

        for kind in basic_kinds {
            if let Some(v) = TokenKind::lex_basic(segment, kind.to_string().as_str(), kind) {
                return Some(v);
            }
        }

        let re_else_if = Regex::new(r#"^else\s*if$"#).unwrap();
        if let Some(v) = TokenKind::lex_regex(segment, re_else_if, TokenKind::ElseIf) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_bool_literal(segment) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_i64_literal(segment) {
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

    fn lex_bool_literal(segment: &str) -> Option<TokenKind> {
        match segment.trim().parse::<bool>() {
            Ok(b) => Some(TokenKind::BoolLiteral(b)),
            Err(_) => None,
        }
    }

    fn lex_i64_literal(segment: &str) -> Option<TokenKind> {
        match segment.trim().parse::<i64>() {
            Ok(i) => Some(TokenKind::I64Literal(i)),
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

                // Removing opening and closing quotes.
                let formatted = &formatted[1..formatted.len() - 1];

                // Handle whitespace characters and escaped quotes and backslashes.
                let formatted = &formatted
                    .replace(r#"\\"#, r#"\"#)
                    .replace(r#"\n"#, "\n")
                    .replace(r#"\r"#, "\r")
                    .replace(r#"\t"#, "\t")
                    .replace(r#"\""#, r#"""#);

                Some(TokenKind::StringLiteral(String::from(formatted)))
            }
            false => None,
        }
    }
}
