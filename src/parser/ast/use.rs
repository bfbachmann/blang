use std::default::Default;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::Position;
use crate::lexer::pos::{Locatable, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::symbol::Symbol;
use crate::parser::error::{ErrorKind, ParseError, ParseResult};
use crate::parser::module::Module;

/// The path to a module that is imported into a program.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ModulePath {
    pub raw: String,
    span: Span,
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
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<ModulePath> {
        match tokens.next() {
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

                // Only perform additional path validation if we're not in test mode.
                #[cfg(not(test))]
                {
                    use std::fs;

                    let full_path = match fs::canonicalize(path) {
                        Ok(p) => p,
                        Err(err) => {
                            return Err(ParseError::new_with_token(
                                ErrorKind::InvalidModPath,
                                format_code!("invalid module path {}: {err}", path).as_str(),
                                token.clone(),
                            ));
                        }
                    };

                    // Make sure the path is valid.
                    match fs::metadata(full_path) {
                        Ok(_) => Ok(ModulePath {
                            raw: path.to_string(),
                            span: token.span,
                        }),

                        Err(_) => Err(ParseError::new_with_token(
                            ErrorKind::ModNotFound,
                            format_code!("module {} was not found", path).as_str(),
                            token.clone(),
                        )),
                    }
                }

                #[cfg(test)]
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
    pub identifiers: Vec<Symbol>,
    span: Span,
}

impl Hash for UsedModule {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.path.hash(state);
        self.maybe_alias.hash(state);
        self.identifiers.hash(state);
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

        if self.identifiers.len() > 0 {
            write!(f, "{{")?;

            for (i, ident) in self.identifiers.iter().enumerate() {
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
    ///     use "path/to/file.bl" @<name>
    ///     use "path/to/file.bl" {<ident>, ...}
    ///     use "path/to/file.bl" @<name> {<ident>, ...}
    ///
    /// where
    /// - `name` is an identifier used to name the module being used
    /// - `ident` is any identifier to import from the given path.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<UsedModule> {
        let start_pos = Module::parse_expecting(tokens, TokenKind::Use)?
            .span
            .start_pos;
        let path = ModulePath::from(tokens)?;

        // Parse the optional `@<name>`.
        let maybe_alias = match tokens.peek_next() {
            Some(Token {
                kind: TokenKind::At,
                ..
            }) => {
                tokens.next();
                Some(Module::parse_identifier(tokens)?)
            }

            _ => None,
        };

        // Parse the identifiers being imported from the module.
        let identifiers = if Module::parse_optional(tokens, TokenKind::LeftBrace).is_some() {
            let mut idents = vec![Symbol::from_identifier(tokens)?];
            while Module::parse_optional(tokens, TokenKind::Comma).is_some() {
                idents.push(Symbol::from_identifier(tokens)?);
            }

            Module::parse_expecting(tokens, TokenKind::RightBrace)?;

            idents
        } else {
            vec![]
        };

        // Make sure that some alias or identifiers were defined.
        if maybe_alias.is_none() && identifiers.is_empty() {
            if let Some(token) = tokens.next() {
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
                start_pos,
                end_pos: path.end_pos().clone(),
            },
            path,
            maybe_alias,
            identifiers,
        })
    }
}
