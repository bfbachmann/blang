use std::collections::HashMap;
use std::fmt;

use lazy_static::lazy_static;
use regex::Regex;

/// Represents any valid token in the language.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum TokenKind {
    // Binary operators
    Plus,
    Minus,
    Asterisk,
    ForwardSlash,
    Percent,
    LogicalAnd,
    LogicalOr,

    // Unary operators
    LogicalNot,
    Ampersand,

    // Variable assignment
    Equal,

    // Comparators
    EqualTo,
    Like,
    NotLike,
    NotEqualTo,
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,

    // Built-in/primitive types and values
    BoolLiteral(bool),
    // The bool here will be true if the "i64" suffix was included in the literal.
    I64Literal(i64, bool),
    // The bool here will be true if the "u64" suffix was included in the literal.
    U64Literal(u64, bool),
    Null,
    StrLiteral(String),
    Fn,
    Struct,
    Enum,

    // Keywords and control flow
    Let,
    Mut,
    If,
    Else,
    Elsif,
    Loop,
    Break,
    Return,
    Continue,
    SizeOf,
    Extern,
    Const,
    ThisType,
    Impl,
    Spec,
    As,

    // Delimiters
    LeftBrace,
    RightBrace,
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    Comma,
    SemiColon,
    Colon,
    DoubleColon,
    Dot,
    Tilde,
    At,
    With,
    DollarSign,

    // User-defined values
    Identifier(String),
}

impl Clone for TokenKind {
    fn clone(&self) -> Self {
        match self {
            TokenKind::Plus => TokenKind::Plus,
            TokenKind::Minus => TokenKind::Minus,
            TokenKind::Asterisk => TokenKind::Asterisk,
            TokenKind::ForwardSlash => TokenKind::ForwardSlash,
            TokenKind::Percent => TokenKind::Percent,
            TokenKind::LogicalAnd => TokenKind::LogicalAnd,
            TokenKind::LogicalOr => TokenKind::LogicalOr,
            TokenKind::LogicalNot => TokenKind::LogicalNot,
            TokenKind::Equal => TokenKind::Equal,
            TokenKind::EqualTo => TokenKind::EqualTo,
            TokenKind::NotEqualTo => TokenKind::NotEqualTo,
            TokenKind::GreaterThan => TokenKind::GreaterThan,
            TokenKind::LessThan => TokenKind::LessThan,
            TokenKind::GreaterThanOrEqual => TokenKind::GreaterThanOrEqual,
            TokenKind::LessThanOrEqual => TokenKind::LessThanOrEqual,
            TokenKind::BoolLiteral(v) => TokenKind::BoolLiteral(*v),
            TokenKind::I64Literal(v, has_suffix) => TokenKind::I64Literal(*v, *has_suffix),
            TokenKind::U64Literal(v, has_suffix) => TokenKind::U64Literal(*v, *has_suffix),
            TokenKind::Null => TokenKind::Null,
            TokenKind::StrLiteral(v) => TokenKind::StrLiteral(v.clone()),
            TokenKind::Fn => TokenKind::Fn,
            TokenKind::Struct => TokenKind::Struct,
            TokenKind::Let => TokenKind::Let,
            TokenKind::Mut => TokenKind::Mut,
            TokenKind::If => TokenKind::If,
            TokenKind::Else => TokenKind::Else,
            TokenKind::Elsif => TokenKind::Elsif,
            TokenKind::Loop => TokenKind::Loop,
            TokenKind::Break => TokenKind::Break,
            TokenKind::Return => TokenKind::Return,
            TokenKind::LeftBrace => TokenKind::LeftBrace,
            TokenKind::RightBrace => TokenKind::RightBrace,
            TokenKind::LeftParen => TokenKind::LeftParen,
            TokenKind::RightParen => TokenKind::RightParen,
            TokenKind::LeftBracket => TokenKind::LeftBracket,
            TokenKind::RightBracket => TokenKind::RightBracket,
            TokenKind::Comma => TokenKind::Comma,
            TokenKind::SemiColon => TokenKind::SemiColon,
            TokenKind::Colon => TokenKind::Colon,
            TokenKind::DoubleColon => TokenKind::DoubleColon,
            TokenKind::Dot => TokenKind::Dot,
            TokenKind::Identifier(v) => TokenKind::Identifier(v.clone()),
            TokenKind::Continue => TokenKind::Continue,
            TokenKind::SizeOf => TokenKind::SizeOf,
            TokenKind::Extern => TokenKind::Extern,
            TokenKind::Tilde => TokenKind::Tilde,
            TokenKind::Const => TokenKind::Const,
            TokenKind::ThisType => TokenKind::ThisType,
            TokenKind::Impl => TokenKind::Impl,
            TokenKind::Enum => TokenKind::Enum,
            TokenKind::At => TokenKind::At,
            TokenKind::Spec => TokenKind::Spec,
            TokenKind::With => TokenKind::With,
            TokenKind::As => TokenKind::As,
            TokenKind::DollarSign => TokenKind::DollarSign,
            TokenKind::Like => TokenKind::Like,
            TokenKind::NotLike => TokenKind::NotLike,
            TokenKind::Ampersand => TokenKind::Ampersand,
        }
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TokenKind::BoolLiteral(b) => write!(f, "{}", b),
            TokenKind::I64Literal(i, has_suffix) => {
                write!(f, "{}{}", i, if *has_suffix { "i64" } else { "" })
            }
            TokenKind::U64Literal(u, has_suffix) => {
                write!(f, "{}{}", u, if *has_suffix { "u64" } else { "" })
            }
            TokenKind::StrLiteral(s) => write!(f, r#""{}""#, s),
            TokenKind::Identifier(s) => write!(f, "{}", s),
            other => write!(f, "{}", other.to_string()),
        }
    }
}

impl TokenKind {
    fn to_string(&self) -> String {
        match self {
            TokenKind::Plus => "+".to_string(),
            TokenKind::Minus => "-".to_string(),
            TokenKind::Asterisk => "*".to_string(),
            TokenKind::ForwardSlash => "/".to_string(),
            TokenKind::Percent => "%".to_string(),
            TokenKind::LogicalAnd => "and".to_string(),
            TokenKind::LogicalOr => "or".to_string(),
            TokenKind::LogicalNot => "!".to_string(),
            TokenKind::Equal => "=".to_string(),
            TokenKind::EqualTo => "==".to_string(),
            TokenKind::NotEqualTo => "!=".to_string(),
            TokenKind::GreaterThan => ">".to_string(),
            TokenKind::LessThan => "<".to_string(),
            TokenKind::GreaterThanOrEqual => ">=".to_string(),
            TokenKind::LessThanOrEqual => "<=".to_string(),
            TokenKind::BoolLiteral(v) => v.to_string(),
            TokenKind::I64Literal(v, _) => v.to_string(),
            TokenKind::U64Literal(v, _) => v.to_string(),
            TokenKind::Null => "NULL".to_string(),
            TokenKind::StrLiteral(v) => v.to_string(),
            TokenKind::Fn => "fn".to_string(),
            TokenKind::Struct => "struct".to_string(),
            TokenKind::Let => "let".to_string(),
            TokenKind::Mut => "mut".to_string(),
            TokenKind::If => "if".to_string(),
            TokenKind::Else => "else".to_string(),
            TokenKind::Elsif => "elsif".to_string(),
            TokenKind::Loop => "loop".to_string(),
            TokenKind::LeftBrace => "{".to_string(),
            TokenKind::RightBrace => "}".to_string(),
            TokenKind::LeftBracket => "[".to_string(),
            TokenKind::RightBracket => "]".to_string(),
            TokenKind::Identifier(v) => v.to_string(),
            TokenKind::LeftParen => "(".to_string(),
            TokenKind::RightParen => ")".to_string(),
            TokenKind::Comma => ",".to_string(),
            TokenKind::SemiColon => ";".to_string(),
            TokenKind::Colon => ":".to_string(),
            TokenKind::DoubleColon => "::".to_string(),
            TokenKind::Dot => ".".to_string(),
            TokenKind::Break => "break".to_string(),
            TokenKind::Return => "return".to_string(),
            TokenKind::Continue => "continue".to_string(),
            TokenKind::SizeOf => "sizeof".to_string(),
            TokenKind::Extern => "extern".to_string(),
            TokenKind::Tilde => "~".to_string(),
            TokenKind::Const => "const".to_string(),
            TokenKind::ThisType => "This".to_string(),
            TokenKind::Impl => "impl".to_string(),
            TokenKind::Enum => "enum".to_string(),
            TokenKind::At => "@".to_string(),
            TokenKind::Spec => "spec".to_string(),
            TokenKind::With => "with".to_string(),
            TokenKind::As => "as".to_string(),
            TokenKind::DollarSign => "$".to_string(),
            TokenKind::Like => "~==".to_string(),
            TokenKind::NotLike => "~!=".to_string(),
            TokenKind::Ampersand => "&".to_string(),
        }
    }

    /// Attempts to lex the given slice into a TokenKind. Returns None if the slice is not a valid
    /// token.
    pub fn from(segment: &str) -> Option<TokenKind> {
        let basic_kinds = HashMap::from([
            (TokenKind::Plus.to_string(), TokenKind::Plus),
            (TokenKind::Minus.to_string(), TokenKind::Minus),
            (TokenKind::Asterisk.to_string(), TokenKind::Asterisk),
            (TokenKind::ForwardSlash.to_string(), TokenKind::ForwardSlash),
            (TokenKind::Percent.to_string(), TokenKind::Percent),
            (TokenKind::LogicalAnd.to_string(), TokenKind::LogicalAnd),
            (TokenKind::LogicalOr.to_string(), TokenKind::LogicalOr),
            (TokenKind::LogicalNot.to_string(), TokenKind::LogicalNot),
            (TokenKind::Equal.to_string(), TokenKind::Equal),
            (TokenKind::Null.to_string(), TokenKind::Null),
            (TokenKind::EqualTo.to_string(), TokenKind::EqualTo),
            (TokenKind::NotEqualTo.to_string(), TokenKind::NotEqualTo),
            (TokenKind::GreaterThan.to_string(), TokenKind::GreaterThan),
            (TokenKind::LessThan.to_string(), TokenKind::LessThan),
            (
                TokenKind::GreaterThanOrEqual.to_string(),
                TokenKind::GreaterThanOrEqual,
            ),
            (
                TokenKind::LessThanOrEqual.to_string(),
                TokenKind::LessThanOrEqual,
            ),
            (TokenKind::Let.to_string(), TokenKind::Let),
            (TokenKind::Mut.to_string(), TokenKind::Mut),
            (TokenKind::If.to_string(), TokenKind::If),
            (TokenKind::Else.to_string(), TokenKind::Else),
            (TokenKind::Elsif.to_string(), TokenKind::Elsif),
            (TokenKind::LeftBrace.to_string(), TokenKind::LeftBrace),
            (TokenKind::RightBrace.to_string(), TokenKind::RightBrace),
            (TokenKind::LeftParen.to_string(), TokenKind::LeftParen),
            (TokenKind::RightParen.to_string(), TokenKind::RightParen),
            (TokenKind::LeftBracket.to_string(), TokenKind::LeftBracket),
            (TokenKind::RightBracket.to_string(), TokenKind::RightBracket),
            (TokenKind::Comma.to_string(), TokenKind::Comma),
            (TokenKind::SemiColon.to_string(), TokenKind::SemiColon),
            (TokenKind::Colon.to_string(), TokenKind::Colon),
            (TokenKind::DoubleColon.to_string(), TokenKind::DoubleColon),
            (TokenKind::Dot.to_string(), TokenKind::Dot),
            (TokenKind::Fn.to_string(), TokenKind::Fn),
            (TokenKind::Struct.to_string(), TokenKind::Struct),
            (TokenKind::Loop.to_string(), TokenKind::Loop),
            (TokenKind::Break.to_string(), TokenKind::Break),
            (TokenKind::Return.to_string(), TokenKind::Return),
            (TokenKind::Continue.to_string(), TokenKind::Continue),
            (TokenKind::SizeOf.to_string(), TokenKind::SizeOf),
            (TokenKind::Extern.to_string(), TokenKind::Extern),
            (TokenKind::Tilde.to_string(), TokenKind::Tilde),
            (TokenKind::Const.to_string(), TokenKind::Const),
            (TokenKind::ThisType.to_string(), TokenKind::ThisType),
            (TokenKind::Impl.to_string(), TokenKind::Impl),
            (TokenKind::Enum.to_string(), TokenKind::Enum),
            (TokenKind::At.to_string(), TokenKind::At),
            (TokenKind::Spec.to_string(), TokenKind::Spec),
            (TokenKind::With.to_string(), TokenKind::With),
            (TokenKind::As.to_string(), TokenKind::As),
            (TokenKind::DollarSign.to_string(), TokenKind::DollarSign),
            (TokenKind::Like.to_string(), TokenKind::Like),
            (TokenKind::NotLike.to_string(), TokenKind::NotLike),
            (TokenKind::Ampersand.to_string(), TokenKind::Ampersand),
        ]);

        // Trim syntactically meaningless whitespace.
        let segment = segment.trim();

        if let Some(v) = basic_kinds.get(segment) {
            return Some(v.clone());
        }

        if let Some(v) = TokenKind::lex_bool_literal(segment) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_i64_literal(segment) {
            return Some(v);
        }

        if let Some(v) = TokenKind::lex_u64_literal(segment) {
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

    fn lex_bool_literal(segment: &str) -> Option<TokenKind> {
        match segment.parse::<bool>() {
            Ok(b) => Some(TokenKind::BoolLiteral(b)),
            Err(_) => None,
        }
    }

    fn lex_i64_literal(segment: &str) -> Option<TokenKind> {
        lazy_static! {
            static ref I64_IDENTIFIER: Regex = Regex::new(r"^[0-9_]+(i64)?$").unwrap();
        }
        match I64_IDENTIFIER.is_match(segment) {
            true => Some(TokenKind::I64Literal(
                segment
                    .replace("i64", "")
                    .chars()
                    .filter(|c| c.is_digit(10))
                    .collect::<String>()
                    .parse::<i64>()
                    .unwrap(),
                segment.ends_with("i64"),
            )),
            false => None,
        }
    }

    fn lex_u64_literal(segment: &str) -> Option<TokenKind> {
        lazy_static! {
            static ref U64_IDENTIFIER: Regex = Regex::new(r"^[0-9_]+(u64)?$").unwrap();
        }
        match U64_IDENTIFIER.is_match(segment) {
            true => Some(TokenKind::U64Literal(
                segment
                    .replace("u64", "")
                    .chars()
                    .filter(|c| c.is_digit(10))
                    .collect::<String>()
                    .parse::<u64>()
                    .unwrap(),
                segment.ends_with("u64"),
            )),
            false => None,
        }
    }

    fn lex_identifier(segment: &str) -> Option<TokenKind> {
        lazy_static! {
            static ref RE_IDENTIFIER: Regex = Regex::new(r"^[a-zA-Z_]+[a-zA-Z0-9_]*$").unwrap();
        }
        match RE_IDENTIFIER.is_match(segment) {
            true => Some(TokenKind::Identifier(String::from(segment))),
            false => None,
        }
    }

    fn lex_string_literal(segment: &str) -> Option<TokenKind> {
        lazy_static! {
            static ref RE_STRING_LITERAL: Regex = Regex::new(r#"^"(?:[^"\\]|\\.)*"$"#).unwrap();
        }

        if !RE_STRING_LITERAL.is_match(segment) {
            return None;
        }

        // Removing opening and closing quotes.
        let segment_chars: Vec<char> = segment.chars().collect();
        let segment_chars = segment_chars[1..segment_chars.len() - 1]
            .iter()
            .cloned()
            .collect::<Vec<char>>();

        // Handle whitespace characters and escaped quotes and backslashes.
        let mut replaced = String::from("");
        let mut i = 0;
        while i < segment_chars.len() {
            let cur_char = segment_chars.get(i).unwrap();
            let next_char = segment_chars.get(i + 1);

            let to_add = match cur_char {
                '\\' => match next_char {
                    Some('\\') => {
                        i += 1;
                        '\\'
                    }
                    Some('n') => {
                        i += 1;
                        '\n'
                    }
                    Some('t') => {
                        i += 1;
                        '\t'
                    }
                    Some('r') => {
                        i += 1;
                        '\r'
                    }
                    Some('"') => {
                        i += 1;
                        '"'
                    }
                    _ => '\\',
                },
                other => *other,
            };

            replaced.push(to_add);
            i += 1;
        }

        Some(TokenKind::StrLiteral(String::from(replaced)))
    }
}
