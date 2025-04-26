use std::default::Default;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::Span;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::symbol::Symbol;
use crate::parser::error::{ErrorKind, ParseError, ParseResult};
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// The path to a module that is imported into a program.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ModulePath {
    pub raw: String,
    pub span: Span,
}

impl Hash for ModulePath {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

locatable_impl!(ModulePath);

impl Display for ModulePath {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, r#""{}""#, self.raw)
    }
}

impl ModulePath {
    /// Parses a module path from the given token stream. A module path is just a string literal.
    pub fn from(parser: &mut FileParser) -> ParseResult<ModulePath> {
        match parser.tokens.next() {
            Some(
                token @ Token {
                    kind: TokenKind::StrLiteral(path),
                    ..
                },
            ) => {
                if path.contains("..") || path.starts_with("/") {
                    return Err(ParseError::new_with_token(
                        ErrorKind::InvalidModPath,
                        format_code!("invalid module path {}", path).as_str(),
                        token.clone(),
                    ));
                }

                Ok(ModulePath {
                    raw: path.to_string(),
                    span: token.span,
                })
            }

            Some(other) => Err(ParseError::new_with_token(
                ErrorKind::InvalidModPath,
                format_code!("expected module path, but found {}", other).as_str(),
                other.clone(),
            )),

            None => Err(ParseError::new(
                ErrorKind::InvalidModPath,
                "expected module path, but found EOF",
                None,
                Default::default(),
            )),
        }
    }
}

/// A module that is imported into a program.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct UsedModule {
    pub path: ModulePath,
    pub maybe_alias: Option<String>,
    pub symbols: Vec<Symbol>,
    pub span: Span,
}

impl Hash for UsedModule {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.path.hash(state);
        self.maybe_alias.hash(state);
        self.symbols.hash(state);
    }
}

locatable_impl!(UsedModule);

impl Display for UsedModule {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "use ")?;

        write!(f, "{} ", self.path)?;

        if let Some(alias) = &self.maybe_alias {
            write!(f, "@{} ", alias)?;
        }

        if self.symbols.len() > 0 {
            write!(f, "{{")?;

            for (i, ident) in self.symbols.iter().enumerate() {
                match i {
                    0 => write!(f, "{}", ident)?,
                    _ => write!(f, ", {}", ident)?,
                }
            }

            write!(f, "}} from ")?;
        }

        Ok(())
    }
}

impl UsedModule {
    /// Parses a `use` statement from the given token sequence. Expects token sequences of
    /// the forms
    ///
    ///     use "path/to/mod" @<name>
    ///     use "path/to/mod" {<ident>, ...}
    ///     use "path/to/mod" @<name> {<ident>, ...}
    ///
    /// where
    /// - `name` is an identifier used to name the module being used
    /// - `ident` is any identifier to import from the given path.
    pub fn parse(parser: &mut FileParser) -> ParseResult<UsedModule> {
        let start_pos = parser.parse_expecting(TokenKind::Use)?.span.start_pos;
        let path = ModulePath::from(parser)?;
        let mut end_pos = path.span.end_pos;

        // Parse the optional `@<name>`.
        let maybe_alias = match parser.tokens.peek_next() {
            Some(Token {
                kind: TokenKind::At,
                ..
            }) => {
                parser.tokens.next();
                let ident = parser.parse_identifier()?;
                end_pos = parser.prev_position();
                Some(ident)
            }

            _ => None,
        };

        // Parse the identifiers being imported from the module.
        let symbols = if parser.parse_optional(TokenKind::LeftBrace).is_some() {
            let mut symbols = vec![Symbol::parse_as_identifier(parser)?];
            while parser.parse_optional(TokenKind::Comma).is_some() {
                symbols.push(Symbol::parse_as_identifier(parser)?);
            }

            end_pos = parser.parse_expecting(TokenKind::RightBrace)?.span.end_pos;

            symbols
        } else {
            vec![]
        };

        // Make sure that some alias or identifiers were defined.
        if maybe_alias.is_none() && symbols.is_empty() {
            if let Some(token) = parser.tokens.next() {
                return Err(ParseError::new_with_token(
                    ErrorKind::UnexpectedToken,
                    format_code!("expected {} or {}, but found {}", "@", "{", token).as_str(),
                    token.clone(),
                ));
            }

            return Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected {} or {}, but found EOF", "@", "{").as_str(),
                None,
                Default::default(),
            ));
        }

        Ok(UsedModule {
            span: Span {
                file_id: parser.file_id,
                start_pos,
                end_pos,
            },
            path,
            maybe_alias,
            symbols,
        })
    }
}
