use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::lexer::pos::Locatable;
use crate::lexer::pos::Position;
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::{ErrorKind, ParseError, ParseResult};
use crate::parser::source::Source;

/// The path to a module that is imported into a program.
#[derive(PartialEq, Clone, Debug)]
pub struct ModulePath {
    pub raw: String,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(ModulePath);

impl ModulePath {
    /// Parses a module path from the given token stream. A module path is just a string literal.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<ModulePath> {
        match tokens.next() {
            Some(
                token @ Token {
                    kind: TokenKind::StrLiteral(path),
                    ..
                },
            ) => Ok(ModulePath {
                raw: path.clone(),
                start_pos: token.start.clone(),
                end_pos: token.end.clone(),
            }),

            Some(other) => Err(ParseError::new_with_token(
                ErrorKind::ExpectedModPath,
                format_code!("expected module path, but found {}", other).as_str(),
                other.clone(),
            )),

            None => Err(ParseError::new(
                ErrorKind::ExpectedModPath,
                "expected module path, but found EOF",
                None,
                Position::default(),
                Position::default(),
            )),
        }
    }
}

/// A module that is imported into a program.
#[derive(PartialEq, Clone, Debug)]
pub struct UsedModule {
    pub path: ModulePath,
    pub maybe_alias: Option<String>,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(UsedModule);

impl UsedModule {
    /// Parses a module reference from the given token stream.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<UsedModule> {
        let path = ModulePath::from(tokens)?;
        let start_pos = path.start_pos().clone();
        let mut end_pos = path.end_pos.clone();
        let maybe_alias = match Source::parse_optional(tokens, TokenKind::As) {
            Some(_) => {
                let name = Source::parse_identifier(tokens)?;
                end_pos = Source::prev_position(tokens);
                Some(name)
            }
            None => None,
        };

        Ok(UsedModule {
            path,
            maybe_alias,
            start_pos,
            end_pos,
        })
    }
}

/// Represents a `use` block that imports foreign modules into a program.
#[derive(PartialEq, Clone, Debug)]
pub struct UseBlock {
    pub used_modules: Vec<UsedModule>,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(UseBlock);

impl Display for UseBlock {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "use {{ <{} used modules> }}", self.used_modules.len())
    }
}

impl UseBlock {
    /// Parses a use block from the given token sequence.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<UseBlock> {
        let start_pos = Source::parse_expecting(tokens, TokenKind::Use)?.start;
        let end_pos;

        let mut used_modules = vec![];
        match Source::parse_optional(tokens, TokenKind::LeftBrace) {
            Some(_) => {
                while !Source::next_token_is(tokens, &TokenKind::RightBrace) {
                    used_modules.push(UsedModule::from(tokens)?);
                }

                end_pos = Source::parse_expecting(tokens, TokenKind::RightBrace)?.end;
            }
            None => {
                let used_mod = UsedModule::from(tokens)?;
                end_pos = used_mod.end_pos().clone();
                used_modules.push(used_mod);
            }
        };

        Ok(UseBlock {
            used_modules,
            start_pos,
            end_pos,
        })
    }
}
