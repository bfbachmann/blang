use std::default::Default;
use std::fmt::{Display, Formatter};
use std::fs;
use std::hash::{Hash, Hasher};

use crate::lexer::pos::Locatable;
use crate::lexer::pos::Position;
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::{ErrorKind, ParseError, ParseResult};
use crate::parser::module::Module;

/// The path to a module that is imported into a program.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ModulePath {
    pub raw: String,
    start_pos: Position,
    end_pos: Position,
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

                let full_path = match fs::canonicalize(path) {
                    Ok(p) => p,
                    Err(_) => {
                        return Err(ParseError::new_with_token(
                            ErrorKind::InvalidModPath,
                            format_code!("invalid module path {}", path).as_str(),
                            token.clone(),
                        ));
                    }
                };

                // Make sure the path is valid.
                match fs::metadata(full_path) {
                    Ok(_) => Ok(ModulePath {
                        raw: path.to_string(),
                        start_pos: token.start.clone(),
                        end_pos: token.end.clone(),
                    }),

                    Err(_) => Err(ParseError::new_with_token(
                        ErrorKind::ModNotFound,
                        format_code!("module {} was not found", path).as_str(),
                        token.clone(),
                    )),
                }
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
                Position::default(),
                Position::default(),
            )),
        }
    }
}

/// A module that is imported into a program.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct UsedModule {
    pub path: ModulePath,
    pub maybe_alias: Option<String>,
    pub identifiers: Vec<String>,
    start_pos: Position,
    end_pos: Position,
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

        write!(f, "{}", self.path)?;

        if let Some(alias) = &self.maybe_alias {
            write!(f, "as {}", alias)?;
        }

        Ok(())
    }
}

impl UsedModule {
    /// Parses a `use` statement from the given token sequence. Expects token sequences of
    /// the forms
    ///
    ///     use <name>: "path/to/file.bl"
    ///     use {<ident>, ...}: "path/to/file.bl"
    ///     use <name> {<ident>, ...}: "path/to/file.bl"
    ///
    /// where
    /// - `name` is an identifier used to name the module being used
    /// - `ident` is any identifier to import from the given path.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<UsedModule> {
        let start_pos = Module::parse_expecting(tokens, TokenKind::Use)?.start;

        // Parse the optional module alias.
        let maybe_alias = match tokens.peek_next() {
            Some(Token {
                kind: TokenKind::Identifier(alias),
                ..
            }) => {
                let result = Some(alias.to_owned());
                tokens.next();
                result
            }

            _ => None,
        };

        // Parse the optional identifiers being imported from the module.
        let identifiers = if Module::parse_optional(tokens, TokenKind::LeftBrace).is_some() {
            let mut idents = vec![Module::parse_identifier(tokens)?];
            while Module::parse_optional(tokens, TokenKind::Comma).is_some() {
                idents.push(Module::parse_identifier(tokens)?);
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
                    format_code!("expected identifier or {}, but found {}", "{", token).as_str(),
                    token.clone(),
                ));
            }

            return Err(ParseError::new(
                ErrorKind::UnexpectedToken,
                format_code!("expected identifier or {}, but found EOF", "{").as_str(),
                None,
                Position::default(),
                Position::default(),
            ));
        }

        Module::parse_expecting(tokens, TokenKind::Colon)?;

        let path = ModulePath::from(tokens)?;

        Ok(UsedModule {
            end_pos: path.end_pos().clone(),
            path,
            maybe_alias,
            identifiers,
            start_pos,
        })
    }
}
