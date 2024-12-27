use std::char::ParseCharError;
use std::fmt;
use std::fmt::{Display, Formatter};
use std::num::{ParseFloatError, ParseIntError};
use std::str::FromStr;

use logos::{FilterResult, Lexer, Logos};

/// Represents any valid token in the language.
#[derive(Logos, Debug, PartialEq, Clone)]
#[logos(skip r"[ \t\f]+")]
#[logos(extras = (usize, usize))]
#[logos(error = LexingError)]
pub enum TokenKind {
    // Whitespace and comments
    #[regex(r"\n", update_line_count)]
    Newline,
    #[regex(r"//[^\n]*")]
    LineComment,
    #[regex(r"/\*(?:[^*]|\*[^/])*\*/", update_line_count)]
    BlockComment,

    // Bitwise operators
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Asterisk,
    #[token("/")]
    ForwardSlash,
    #[token("%")]
    Percent,
    #[token("+=")]
    PlusEqual,
    #[token("-=")]
    MinusEqual,
    #[token("*=")]
    AsteriskEqual,
    #[token("/=")]
    ForwardSlashEqual,
    #[token("%=")]
    PercentEqual,
    #[token("&&")]
    LogicalAnd,
    #[token("||")]
    LogicalOr,
    #[token("&&=")]
    LogicalAndEqual,
    #[token("||=")]
    LogicalOrEqual,
    #[token("band")]
    BitwiseAnd,
    #[token("bor")]
    BitwiseOr,
    #[token("bxor")]
    BitwiseXor,
    #[token("bls")]
    BitwiseLeftShift,
    #[token("brs")]
    BitwiseRightShift,
    #[token("band=")]
    BitwiseAndEqual,
    #[token("bor=")]
    BitwiseOrEqual,
    #[token("bxor=")]
    BitwiseXorEqual,
    #[token("bls=")]
    BitwiseLeftShiftEqual,
    #[token("brs=")]
    BitwiseRightShiftEqual,

    // Unary operators
    #[token("!")]
    LogicalNot,
    #[token("bnot")]
    BitwiseNot,
    #[token("&")]
    Ref,
    #[token("&mut")]
    RefMut,
    #[token("^")]
    Deref,

    // Variable assignment
    #[token("=")]
    Equal,

    // Comparators
    #[token("==")]
    EqualTo,
    #[token("~~")]
    Like,
    #[token("!~")]
    NotLike,
    #[token("!=")]
    NotEqualTo,
    #[token(">")]
    GreaterThan,
    #[token("<")]
    LessThan,
    #[token(">=")]
    GreaterThanOrEqual,
    #[token("<=")]
    LessThanOrEqual,

    // Built-in/primitive types and values
    #[token("false", |_| false)]
    #[token("true", |_| true)]
    BoolLiteral(bool),
    #[regex(r"((0x[0-9a-f_]+)|(0b[01_]+)|([0-9][0-9_]*))u8", lex_u8_literal)]
    U8Literal(u8),
    #[regex(r"((0x[0-9a-f_]+)|(0b[01_]+)|([0-9][0-9_]*))i8", lex_i8_literal)]
    I8Literal(i8),
    #[regex(r"((0x[0-9a-f_]+)|(0b[01_]+)|([0-9][0-9_]*))u16", lex_u16_literal)]
    U16Literal(u16),
    #[regex(r"((0x[0-9a-f_]+)|(0b[01_]+)|([0-9][0-9_]*))i16", lex_i16_literal)]
    I16Literal(i16),
    #[regex(r"((0x[0-9a-f_]+)|(0b[01_]+)|([0-9][0-9_]*))u32", lex_u32_literal)]
    U32Literal(u32),
    #[regex(r"((0x[0-9a-f_]+)|(0b[01_]+)|([0-9][0-9_]*))i32", lex_i32_literal)]
    I32Literal(i32),
    #[regex(r"\d+[0-9_]*\.[0-9_]*(e-?[0-9_]+)?f32", lex_f32_literal)]
    F32Literal(f32),
    #[regex(r"((0x[0-9a-f_]+)|(0b[01_]+)|([0-9][0-9_]*))i64", lex_i64_literal)]
    I64Literal(i64),
    #[regex(r"((0x[0-9a-f_]+)|(0b[01_]+)|([0-9][0-9_]*))u64", lex_u64_literal)]
    U64Literal(u64),
    #[regex(r"\d+[0-9_]*\.[0-9_]*(e-?[0-9_]+)?(f64)?", lex_f64_literal)]
    F64Literal((f64, bool)),
    #[regex(r"((0x[0-9a-f_]+)|(0b[01_]+)|([0-9][0-9_]*))(int)?", lex_int_literal)]
    IntLiteral((i64, bool)),
    #[regex(r"((0x[0-9a-f_]+)|(0b[01_]+)|([0-9][0-9_]*))uint", lex_uint_literal)]
    UintLiteral(u64),
    #[regex(r#""(?:[^"]|\\.)*""#, lex_str_lit)]
    StrLiteral(String),
    #[regex(
        r#"'([^'\\]|\\[nrt0'\\]|\\x[0-9A-Fa-f]{2}|\\u[0-9A-Fa-f]{1,6})'"#,
        lex_char_lit
    )]
    CharLiteral(char),
    #[token("fn")]
    Fn,
    #[token("struct")]
    Struct,
    #[token("enum")]
    Enum,

    // Keywords and control flow
    #[token("pub")]
    Pub,
    #[token("let")]
    Let,
    #[token("mut")]
    Mut,
    #[token("if")]
    If,
    #[token("else")]
    Else,
    #[token("match")]
    Match,
    #[token("case")]
    Case,
    #[token("for")]
    For,
    #[token("while")]
    While,
    #[token("loop")]
    Loop,
    #[token("break")]
    Break,
    #[token("return")]
    Return,
    #[token("continue")]
    Continue,
    #[token("sizeof")]
    SizeOf,
    #[token("extern")]
    Extern,
    #[token("const")]
    Const,
    #[token("impl")]
    Impl,
    #[token("spec")]
    Spec,
    #[token("as")]
    As,
    #[token("use")]
    Use,
    #[token("from")]
    From,
    #[token("yield")]
    Yield,

    // Delimiters
    #[token("{")]
    LeftBrace,
    #[token("}")]
    RightBrace,
    #[token("(")]
    LeftParen,
    #[token(")")]
    RightParen,
    #[token(".(")]
    BeginIndex,
    #[token("[")]
    LeftBracket,
    #[token("]")]
    RightBracket,
    #[token(",")]
    Comma,
    #[token(";")]
    SemiColon,
    #[token(":")]
    Colon,
    #[token("->")]
    Arrow,
    #[token("::")]
    DoubleColon,
    #[token(".")]
    Dot,
    #[token("@")]
    At,
    #[token("with")]
    With,
    #[token("$")]
    DollarSign,

    // User-defined values
    #[regex(r#"[a-zA-Z_]+[a-zA-Z0-9_]*"#, |lex| lex.slice().to_owned())]
    Identifier(String),
}

impl TokenKind {
    fn to_string(&self) -> String {
        match self {
            TokenKind::Newline => "\n".to_string(),
            TokenKind::LineComment | TokenKind::BlockComment => "<comment>".to_string(),
            TokenKind::Plus => "+".to_string(),
            TokenKind::Minus => "-".to_string(),
            TokenKind::Asterisk => "*".to_string(),
            TokenKind::ForwardSlash => "/".to_string(),
            TokenKind::Percent => "%".to_string(),
            TokenKind::PlusEqual => "+=".to_string(),
            TokenKind::MinusEqual => "-=".to_string(),
            TokenKind::AsteriskEqual => "*=".to_string(),
            TokenKind::ForwardSlashEqual => "/=".to_string(),
            TokenKind::PercentEqual => "%=".to_string(),
            TokenKind::LogicalAnd => "and".to_string(),
            TokenKind::LogicalOr => "or".to_string(),
            TokenKind::LogicalAndEqual => "&&=".to_string(),
            TokenKind::LogicalOrEqual => "||=".to_string(),
            TokenKind::LogicalNot => "!".to_string(),
            TokenKind::BitwiseNot => "bnot".to_string(),
            TokenKind::BitwiseAnd => "band".to_string(),
            TokenKind::BitwiseOr => "bor".to_string(),
            TokenKind::BitwiseXor => "bxor".to_string(),
            TokenKind::BitwiseLeftShift => "bls".to_string(),
            TokenKind::BitwiseRightShift => "brs".to_string(),
            TokenKind::BitwiseAndEqual => "band=".to_string(),
            TokenKind::BitwiseOrEqual => "bor=".to_string(),
            TokenKind::BitwiseXorEqual => "bxor=".to_string(),
            TokenKind::BitwiseLeftShiftEqual => "bls=".to_string(),
            TokenKind::BitwiseRightShiftEqual => "brs=".to_string(),
            TokenKind::Equal => "=".to_string(),
            TokenKind::EqualTo => "==".to_string(),
            TokenKind::NotEqualTo => "!=".to_string(),
            TokenKind::GreaterThan => ">".to_string(),
            TokenKind::LessThan => "<".to_string(),
            TokenKind::GreaterThanOrEqual => ">=".to_string(),
            TokenKind::LessThanOrEqual => "<=".to_string(),
            TokenKind::BoolLiteral(v) => v.to_string(),
            TokenKind::I8Literal(v) => v.to_string(),
            TokenKind::U8Literal(v) => v.to_string(),
            TokenKind::I16Literal(v) => v.to_string(),
            TokenKind::U16Literal(v) => v.to_string(),
            TokenKind::I32Literal(v) => v.to_string(),
            TokenKind::U32Literal(v) => v.to_string(),
            TokenKind::F32Literal(v) => v.to_string(),
            TokenKind::I64Literal(v) => v.to_string(),
            TokenKind::U64Literal(v) => v.to_string(),
            TokenKind::F64Literal((v, has_suffix)) => format!(
                "{}{}",
                v.to_string(),
                match has_suffix {
                    true => "f64",
                    false => "",
                }
            )
            .to_string(),
            TokenKind::IntLiteral((v, has_suffix)) => format!(
                "{}{}",
                v.to_string(),
                match has_suffix {
                    true => "int",
                    false => "",
                }
            )
            .to_string(),
            TokenKind::UintLiteral(v) => v.to_string(),
            TokenKind::StrLiteral(v) => v.to_owned(),
            TokenKind::CharLiteral(v) => v.to_string(),
            TokenKind::Fn => "fn".to_string(),
            TokenKind::Struct => "struct".to_string(),
            TokenKind::Let => "let".to_string(),
            TokenKind::Pub => "pub".to_string(),
            TokenKind::Mut => "mut".to_string(),
            TokenKind::If => "if".to_string(),
            TokenKind::Else => "else".to_string(),
            TokenKind::Match => "match".to_string(),
            TokenKind::Case => "case".to_string(),
            TokenKind::For => "for".to_string(),
            TokenKind::While => "while".to_string(),
            TokenKind::Loop => "loop".to_string(),
            TokenKind::LeftBrace => "{".to_string(),
            TokenKind::RightBrace => "}".to_string(),
            TokenKind::BeginIndex => ".(".to_string(),
            TokenKind::LeftBracket => "[".to_string(),
            TokenKind::RightBracket => "]".to_string(),
            TokenKind::Identifier(v) => v.to_string(),
            TokenKind::LeftParen => "(".to_string(),
            TokenKind::RightParen => ")".to_string(),
            TokenKind::Comma => ",".to_string(),
            TokenKind::SemiColon => ";".to_string(),
            TokenKind::Colon => ":".to_string(),
            TokenKind::Arrow => "->".to_string(),
            TokenKind::DoubleColon => "::".to_string(),
            TokenKind::Dot => ".".to_string(),
            TokenKind::Break => "break".to_string(),
            TokenKind::Return => "return".to_string(),
            TokenKind::Continue => "continue".to_string(),
            TokenKind::SizeOf => "sizeof".to_string(),
            TokenKind::Extern => "extern".to_string(),
            TokenKind::Const => "const".to_string(),
            TokenKind::Impl => "impl".to_string(),
            TokenKind::Enum => "enum".to_string(),
            TokenKind::At => "@".to_string(),
            TokenKind::Spec => "spec".to_string(),
            TokenKind::With => "with".to_string(),
            TokenKind::As => "as".to_string(),
            TokenKind::DollarSign => "$".to_string(),
            TokenKind::Like => "~~".to_string(),
            TokenKind::NotLike => "!~".to_string(),
            TokenKind::Ref => "&".to_string(),
            TokenKind::RefMut => "&mut".to_string(),
            TokenKind::Deref => "^".to_string(),
            TokenKind::Use => "use".to_string(),
            TokenKind::From => "from".to_string(),
            TokenKind::Yield => "yield".to_string(),
        }
    }
}

/// Updates the line counter in the lexer based on the number of newlines
/// in the lexer slice.
fn update_line_count(lexer: &mut Lexer<TokenKind>) {
    let comment = lexer.slice();

    // Update the lexer line counter with the newlines in the token.
    let newlines = comment.chars().filter(|&c| c == '\n').count();
    lexer.extras.0 += newlines;

    // Set the lexer's last newline offset if there are new newlines.
    if newlines > 0 {
        lexer.extras.1 = lexer.span().start + comment.rfind('\n').unwrap();
    }
}

fn lex_str_lit(lexer: &mut Lexer<TokenKind>) -> String {
    let str_lit = lexer.slice();

    update_line_count(lexer);

    // Remove quotes.
    let chars: Vec<char> = str_lit[1..str_lit.len() - 1].chars().collect();

    // Handle escape sequences and newlines.
    let mut replaced = String::from("");
    let mut i = 0;
    'outer: while i < chars.len() {
        let cur_char = chars.get(i).unwrap();
        let next_char = chars.get(i + 1);

        let to_add = match cur_char {
            // Handle potential escape sequence.
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
                Some('0') => {
                    i += 1;
                    '\0'
                }
                Some('\n') => {
                    // This is an escaped newline. We need to trim the newline
                    // and all whitespace that immediately follows it.
                    while i < chars.len() - 1 {
                        i += 1;
                        if !chars.get(i).unwrap().is_whitespace() {
                            // We've found the first non-whitespace char that
                            // follows the escaped newline. Now we can continue
                            // on the outer loop.
                            continue 'outer;
                        }
                    }

                    // If we get here, it means we've reached the end of the
                    // string literal, so we can just return.
                    return replaced;
                }
                _ => '\\',
            },

            other => *other,
        };

        replaced.push(to_add);
        i += 1;
    }

    replaced
}

fn lex_char_lit(lexer: &mut Lexer<TokenKind>) -> FilterResult<char, LexingError> {
    let slice = lexer.slice();

    // Remove quotes.
    let char_lit = slice[1..slice.len() - 1].chars().as_str();

    match char_lit {
        // Escape sequences.
        "\\n" => FilterResult::Emit('\n'),
        "\\t" => FilterResult::Emit('\t'),
        "\\r" => FilterResult::Emit('\r'),
        "\\0" => FilterResult::Emit('\0'),
        "\\'" => FilterResult::Emit('\''),
        "\\\\" => FilterResult::Emit('\\'),

        // Hex and unicode escape sequences with \x and \u.
        _ if char_lit.starts_with("\\x") || char_lit.starts_with("\\u") => {
            match u32::from_str_radix(&char_lit[2..], 16) {
                Ok(char_code) => match char::from_u32(char_code) {
                    Some(c) => FilterResult::Emit(c),
                    None => FilterResult::Error(LexingError::InvalidCharCode(char_code)),
                },
                Err(e) => FilterResult::Error(LexingError::InvalidInt(e)),
            }
        }

        // Regular ASCII literals.
        _ => match char::from_str(char_lit) {
            Ok(c) => FilterResult::Emit(c),
            Err(e) => FilterResult::Error(LexingError::InvalidChar(e)),
        },
    }
}

/// Lexes an integer literal of type `$t` from string `$s`. Supports decimal, hex,
/// and binary literals.
macro_rules! lex_int {
    ($t:ty, $s:ident) => {
        'result: {
            if $s.len() > 2 {
                match (&$s[0..2], &$s[2..]) {
                    ("0x", hex) => match <$t>::from_str_radix(hex, 16) {
                        Ok(u) => break 'result FilterResult::Emit(u),
                        Err(e) => break 'result FilterResult::Error(LexingError::InvalidInt(e)),
                    },
                    ("0b", binary) => match <$t>::from_str_radix(binary, 2) {
                        Ok(u) => break 'result FilterResult::Emit(u),
                        Err(e) => break 'result FilterResult::Error(LexingError::InvalidInt(e)),
                    },
                    _ => {}
                };
            }

            match $s.parse::<$t>() {
                Ok(i) => FilterResult::Emit(i),
                Err(e) => FilterResult::Error(LexingError::InvalidInt(e)),
            }
        }
    };
}

fn lex_u8_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<u8, LexingError> {
    let lit = lexer.slice().trim_end_matches("u8").replace("_", "");
    lex_int!(u8, lit)
}

fn lex_i8_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<i8, LexingError> {
    let lit = lexer.slice().trim_end_matches("i8").replace("_", "");
    lex_int!(i8, lit)
}

fn lex_u16_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<u16, LexingError> {
    let lit = lexer.slice().trim_end_matches("u16").replace("_", "");
    lex_int!(u16, lit)
}

fn lex_i16_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<i16, LexingError> {
    let lit = lexer.slice().trim_end_matches("i16").replace("_", "");
    lex_int!(i16, lit)
}

fn lex_u32_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<u32, LexingError> {
    let lit = lexer.slice().trim_end_matches("u32").replace("_", "");
    lex_int!(u32, lit)
}

fn lex_i32_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<i32, LexingError> {
    let lit = lexer.slice().trim_end_matches("i32").replace("_", "");
    lex_int!(i32, lit)
}

fn lex_f32_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<f32, LexingError> {
    match lexer
        .slice()
        .trim_end_matches("f32")
        .replace("_", "")
        .parse::<f32>()
    {
        Ok(i) => FilterResult::Emit(i),
        Err(e) => {
            return FilterResult::Error(LexingError::InvalidF64(e));
        }
    }
}

fn lex_i64_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<i64, LexingError> {
    let lit = lexer.slice().trim_end_matches("i64").replace("_", "");
    lex_int!(i64, lit)
}

fn lex_u64_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<u64, LexingError> {
    let lit = lexer.slice().trim_end_matches("u64").replace("_", "");
    lex_int!(u64, lit)
}

fn lex_uint_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<u64, LexingError> {
    let lit = lexer.slice().trim_end_matches("uint").replace("_", "");
    lex_int!(u64, lit)
}

fn lex_int_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<(i64, bool), LexingError> {
    let slice = lexer.slice();
    let has_suffix = slice.contains("int");
    let lit = lexer.slice().trim_end_matches("int").replace("_", "");
    match lex_int!(i64, lit) {
        FilterResult::Emit(i) => FilterResult::Emit((i, has_suffix)),
        FilterResult::Error(e) => FilterResult::Error(e),
        _ => unreachable!(),
    }
}

fn lex_f64_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<(f64, bool), LexingError> {
    let slice = lexer.slice();
    let has_suffix = slice.contains("f64");
    match lexer
        .slice()
        .trim_end_matches("f64")
        .replace("_", "")
        .parse::<f64>()
    {
        Ok(f) => FilterResult::Emit((f, has_suffix)),
        Err(e) => {
            return FilterResult::Error(LexingError::InvalidF64(e));
        }
    }
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            TokenKind::BoolLiteral(b) => write!(f, "{}", b),
            TokenKind::StrLiteral(s) => write!(f, r#""{}""#, s),
            TokenKind::Identifier(s) => write!(f, "{}", s),
            other => write!(f, "{}", other.to_string()),
        }
    }
}

#[derive(Debug, PartialEq, Clone, Default)]
pub enum LexingError {
    InvalidInt(ParseIntError),
    InvalidF64(ParseFloatError),
    InvalidChar(ParseCharError),
    InvalidCharCode(u32),
    #[default]
    Default,
}

impl Display for LexingError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            LexingError::InvalidInt(e) => write!(f, "{}", e),
            LexingError::InvalidF64(e) => write!(f, "{}", e),
            LexingError::InvalidChar(e) => write!(f, "{}", e),
            LexingError::InvalidCharCode(c) => write!(f, "invalid character code {c}"),
            LexingError::Default => write!(f, "invalid token"),
        }
    }
}

impl From<ParseFloatError> for LexingError {
    fn from(e: ParseFloatError) -> Self {
        LexingError::InvalidF64(e)
    }
}

impl From<ParseIntError> for LexingError {
    fn from(e: ParseIntError) -> Self {
        LexingError::InvalidInt(e)
    }
}
