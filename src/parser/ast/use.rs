use std::fmt::{Display, Formatter};
use std::fs;
use std::hash::{Hash, Hasher};

use colored::Colorize;

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
                if path.contains("..") || path.starts_with("/") || path.starts_with(".") {
                    return Err(ParseError::new_with_token(
                        ErrorKind::InvalidModPath,
                        format_code!("invalid module path {}", path).as_str(),
                        token.clone(),
                    ));
                }

                let path = match fs::canonicalize(path) {
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
                match fs::metadata(path.clone()) {
                    Ok(_) => Ok(ModulePath {
                        raw: path.to_str().unwrap().to_string(),
                        start_pos: token.start.clone(),
                        end_pos: token.end.clone(),
                    }),

                    Err(_) => Err(ParseError::new_with_token(
                        ErrorKind::ModNotFound,
                        format_code!("module {} was not found", path.display()).as_str(),
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
    ///     use "path/to/file.bl"
    ///     use "path/to/file.bl" as <alias>
    ///     use {<ident>, ...} from "path/to/file.bl"
    ///     use * from "path/to/file.bl"
    ///
    /// where
    /// - `ident` is any identifier to import from the given path
    /// - `alias` is any identifier that will serve as an alias for the module.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<UsedModule> {
        let start_pos = Module::parse_expecting(tokens, TokenKind::Use)?.start;
        let end_pos;

        match Module::parse_optional(tokens, TokenKind::LeftBrace) {
            // If the next token is `{`, we'll assume we're parsing a `use` statement of
            // the form `use {<ident>, ...} from "<path>"`.
            Some(_) => {
                // Parse all the identifiers being imported.
                let mut identifiers = vec![];
                while !Module::next_token_is(tokens, &TokenKind::RightBrace) {
                    // Parse the next identifier.
                    identifiers.push(Module::parse_identifier(tokens)?);

                    // If there is no comma following the identifier, then we've reached the
                    // end of the identifiers list.
                    if Module::parse_optional(tokens, TokenKind::Comma).is_none() {
                        break;
                    };
                }

                // Parse the remaining `} from "<path>"`.
                Module::parse_expecting(tokens, TokenKind::RightBrace)?.end;
                Module::parse_expecting(tokens, TokenKind::From)?;
                let path = ModulePath::from(tokens)?;
                end_pos = path.end_pos().clone();

                Ok(UsedModule {
                    path,
                    maybe_alias: None,
                    identifiers,
                    start_pos,
                    end_pos,
                })
            }

            // In this case, we'll assume we're just parsing a `use` statement of the forms
            //
            //      use * from "<path>"
            //      use "<path>"
            //      use "<path>" as <alias>
            None => {
                // Handle the special case of the wildcard `*` import.
                if Module::parse_optional(tokens, TokenKind::Asterisk).is_some() {
                    Module::parse_expecting(tokens, TokenKind::From)?;

                    let path = ModulePath::from(tokens)?;
                    end_pos = path.end_pos().clone();
                    Ok(UsedModule {
                        path,
                        maybe_alias: None,
                        identifiers: vec!["*".into()],
                        start_pos,
                        end_pos,
                    })
                } else {
                    let path = ModulePath::from(tokens)?;
                    let (maybe_alias, end_pos) = match Module::parse_optional(tokens, TokenKind::As)
                    {
                        Some(_) => {
                            let alias = Module::parse_identifier(tokens)?;
                            (Some(alias), Module::prev_position(tokens))
                        }
                        None => (None, path.end_pos().clone()),
                    };

                    Ok(UsedModule {
                        path,
                        maybe_alias,
                        identifiers: vec![],
                        start_pos,
                        end_pos,
                    })
                }
            }
        }
    }
}
