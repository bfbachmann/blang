use lazy_static::lazy_static;
use regex::Regex;
use std::fmt;

/// Represents any valid token in the language.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TokenKind {
    // Operators
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,

    // Variable assignment
    Equal,

    // Comparators
    Equals,
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,

    // Built-in/primitive types
    Bool,
    BoolLiteral(bool),
    Int,
    IntLiteral(i64),
    String,
    StringLiteral(String),
    Function,

    // Keywords and control flow
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
    Colon,

    // User-defined values
    Identifier(String),
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TokenKind::BoolLiteral(b) => write!(f, "boolean literal {}", b.to_string()),
            TokenKind::IntLiteral(i) => write!(f, "integer literal {}", i.to_string()),
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
            TokenKind::Equal => "=".to_string(),
            TokenKind::Equals => "==".to_string(),
            TokenKind::GreaterThan => ">".to_string(),
            TokenKind::LessThan => "<".to_string(),
            TokenKind::GreaterThanOrEqual => ">=".to_string(),
            TokenKind::LessThanOrEqual => "<=".to_string(),
            TokenKind::Bool => "bool".to_string(),
            TokenKind::BoolLiteral(v) => v.to_string(),
            TokenKind::IntLiteral(v) => v.to_string(),
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
            TokenKind::Int => "int".to_string(),
            TokenKind::OpenParen => "(".to_string(),
            TokenKind::CloseParen => ")".to_string(),
            TokenKind::Comma => ",".to_string(),
            TokenKind::SemiColon => ";".to_string(),
            TokenKind::Colon => ":".to_string(),
            TokenKind::Break => "break".to_string(),
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

    /// Returns the number of characters in the token.
    pub fn len(&self) -> usize {
        self.to_string().len()
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
            TokenKind::Equal,
            TokenKind::Int,
            TokenKind::Bool,
            TokenKind::Equals,
            TokenKind::GreaterThan,
            TokenKind::LessThan,
            TokenKind::GreaterThanOrEqual,
            TokenKind::LessThanOrEqual,
            TokenKind::If,
            TokenKind::Else,
            TokenKind::String,
            TokenKind::BeginClosure,
            TokenKind::EndClosure,
            TokenKind::OpenParen,
            TokenKind::CloseParen,
            TokenKind::Comma,
            TokenKind::SemiColon,
            TokenKind::Colon,
            TokenKind::Function,
            TokenKind::Loop,
            TokenKind::Break,
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

    fn lex_bool_literal(segment: &str) -> Option<TokenKind> {
        match segment.trim().parse::<bool>() {
            Ok(b) => Some(TokenKind::BoolLiteral(b)),
            Err(_) => None,
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
