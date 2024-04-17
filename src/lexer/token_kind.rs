use std::fmt;
use std::fmt::{Display, Formatter};
use std::num::{ParseFloatError, ParseIntError};

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

    // Binary operators
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
    #[token("and")]
    LogicalAnd,
    #[token("or")]
    LogicalOr,

    // Unary operators
    #[token("!")]
    LogicalNot,
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
    #[regex(r"[0-9][0-9_]*u8", lex_u8_literal)]
    U8Literal(u8),
    #[regex(r"[0-9][0-9_]*i8", lex_i8_literal)]
    I8Literal(i8),
    #[regex(r"[0-9][0-9_]*u32", lex_u32_literal)]
    U32Literal(u32),
    #[regex(r"[0-9][0-9_]*i32", lex_i32_literal)]
    I32Literal(i32),
    #[regex(r"\d+[0-9_]*\.[0-9_]*(e-?[0-9_]+)?f32", lex_f32_literal)]
    F32Literal(f32),
    #[regex(r"[0-9][0-9_]*i64", lex_i64_literal)]
    I64Literal(i64),
    #[regex(r"[0-9][0-9_]*u64", lex_u64_literal)]
    U64Literal(u64),
    #[regex(r"\d+[0-9_]*\.[0-9_]*(e-?[0-9_]+)?(f64)?", lex_f64_literal)]
    F64Literal((f64, bool)),
    #[regex(r"[0-9][0-9_]*(int)?", lex_int_literal)]
    IntLiteral((i64, bool)),
    #[regex(r"[0-9][0-9_]*uint", lex_uint_literal)]
    UintLiteral(u64),
    #[regex(r#""(?:[^"]|\\.)*""#, lex_str_lit)]
    StrLiteral(String),
    #[token("fn")]
    Fn,
    #[token("struct")]
    Struct,
    #[token("enum")]
    Enum,

    // Keywords and control flow
    #[token("let")]
    Let,
    #[token("mut")]
    Mut,
    #[token("if")]
    If,
    #[token("else")]
    Else,
    #[token("elsif")]
    Elsif,
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
            TokenKind::LogicalNot => "!".to_string(),
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
            TokenKind::Fn => "fn".to_string(),
            TokenKind::Struct => "struct".to_string(),
            TokenKind::Let => "let".to_string(),
            TokenKind::Mut => "mut".to_string(),
            TokenKind::If => "if".to_string(),
            TokenKind::Else => "else".to_string(),
            TokenKind::Elsif => "elsif".to_string(),
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

fn lex_u8_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<u8, LexingError> {
    match lexer
        .slice()
        .trim_end_matches("u8")
        .replace("_", "")
        .parse::<u8>()
    {
        Ok(i) => FilterResult::Emit(i),
        Err(e) => {
            return FilterResult::Error(LexingError::InvalidInt(e));
        }
    }
}

fn lex_i8_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<i8, LexingError> {
    match lexer
        .slice()
        .trim_end_matches("i8")
        .replace("_", "")
        .parse::<i8>()
    {
        Ok(i) => FilterResult::Emit(i),
        Err(e) => {
            return FilterResult::Error(LexingError::InvalidInt(e));
        }
    }
}

fn lex_u32_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<u32, LexingError> {
    match lexer
        .slice()
        .trim_end_matches("u32")
        .replace("_", "")
        .parse::<u32>()
    {
        Ok(i) => FilterResult::Emit(i),
        Err(e) => {
            return FilterResult::Error(LexingError::InvalidInt(e));
        }
    }
}

fn lex_i32_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<i32, LexingError> {
    match lexer
        .slice()
        .trim_end_matches("i32")
        .replace("_", "")
        .parse::<i32>()
    {
        Ok(i) => FilterResult::Emit(i),
        Err(e) => {
            return FilterResult::Error(LexingError::InvalidInt(e));
        }
    }
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
    match lexer
        .slice()
        .trim_end_matches("i64")
        .replace("_", "")
        .parse::<i64>()
    {
        Ok(i) => FilterResult::Emit(i),
        Err(e) => {
            return FilterResult::Error(LexingError::InvalidInt(e));
        }
    }
}

fn lex_u64_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<u64, LexingError> {
    match lexer
        .slice()
        .trim_end_matches("u64")
        .replace("_", "")
        .parse::<u64>()
    {
        Ok(i) => FilterResult::Emit(i),
        Err(e) => {
            return FilterResult::Error(LexingError::InvalidInt(e));
        }
    }
}

fn lex_uint_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<u64, LexingError> {
    match lexer
        .slice()
        .trim_end_matches("uint")
        .replace("_", "")
        .parse::<u64>()
    {
        Ok(i) => FilterResult::Emit(i),
        Err(e) => {
            return FilterResult::Error(LexingError::InvalidInt(e));
        }
    }
}

fn lex_int_literal(lexer: &mut Lexer<TokenKind>) -> FilterResult<(i64, bool), LexingError> {
    let slice = lexer.slice();
    let has_suffix = slice.contains("int");
    match lexer
        .slice()
        .trim_end_matches("int")
        .replace("_", "")
        .parse::<i64>()
    {
        Ok(i) => FilterResult::Emit((i, has_suffix)),
        Err(e) => {
            return FilterResult::Error(LexingError::InvalidInt(e));
        }
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
    #[default]
    Default,
}

impl Display for LexingError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            LexingError::InvalidInt(e) => write!(f, "{}", e),
            LexingError::InvalidF64(e) => write!(f, "{}", e),
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
