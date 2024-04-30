use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

/// Represents a a named value. These can be variables, variable member accesses, functions,
/// constants, or types.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Symbol {
    /// Some symbols will be accessed from other imported modules. For example:
    ///
    ///     use "my_project/my_file.bl"
    ///     // ...
    ///         @my_file.some_fn(...)
    ///
    /// In these cases, the module path specified with `@<mod_name>` is included
    /// in the symbol name and will be available via this field.
    pub maybe_mod_name: Option<String>,
    pub name: String,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}",
            match &self.maybe_mod_name {
                Some(name) => format!("@{}.", name),
                None => "".to_string(),
            },
            self.name
        )
    }
}

impl Hash for Symbol {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

locatable_impl!(Symbol);

impl Symbol {
    /// Creates a new symbol.
    #[cfg(test)]
    pub fn new(name: &str, start_pos: Position, end_pos: Position) -> Self {
        Symbol {
            maybe_mod_name: None,
            name: name.to_string(),
            start_pos,
            end_pos,
        }
    }

    /// Creates a new symbol with the given name and mod name, and with default
    /// start and end positions.
    pub fn new_with_mod(name: &str, mod_name: &str) -> Symbol {
        Symbol {
            maybe_mod_name: Some(mod_name.to_string()),
            name: name.to_string(),
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Creates a new symbol with default (zero) start and end positions.
    #[cfg(test)]
    pub fn new_with_default_pos(name: &str) -> Self {
        Symbol {
            maybe_mod_name: None,
            name: name.to_string(),
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Attempts to parse a symbol from the given token sequence. Expects token
    /// sequences of the forms:
    ///
    ///     <ident>
    ///     @<mod_name>.<ident>
    ///
    /// where
    /// - `ident` is an identifier
    /// - `mod_name` is an identifier that represents the module the symbol comes from.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Symbol> {
        let start_pos = Module::current_position(tokens);

        // Parse the optional module name.
        let maybe_mod_name = if Module::parse_optional(tokens, TokenKind::At).is_some() {
            let mod_name = Module::parse_identifier(tokens)?;
            Module::parse_expecting(tokens, TokenKind::Dot)?;
            Some(mod_name)
        } else {
            None
        };

        // Parse the symbol name.
        let name = Module::parse_identifier(tokens)?;

        Ok(Symbol {
            maybe_mod_name,
            name,
            start_pos,
            end_pos: Module::prev_position(tokens),
        })
    }
}
