use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

/// Represents a a named value. These can be variables, variable member accesses, functions,
/// constants, or types.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Symbol {
    pub name: String,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
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
            name: name.to_string(),
            start_pos,
            end_pos,
        }
    }

    /// Creates a new symbol with default (zero) start and end positions.
    #[cfg(test)]
    pub fn new_with_default_pos(name: &str) -> Self {
        Symbol {
            name: name.to_string(),
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Attempts to parse a symbol composed only of a single identifier from the given token sequence.
    pub fn from_identifier(tokens: &mut Stream<Token>) -> ParseResult<Symbol> {
        let start_pos = Module::current_position(tokens);
        let name = Module::parse_identifier(tokens)?;
        Ok(Symbol {
            name,
            start_pos,
            end_pos: Module::prev_position(tokens),
        })
    }
}
