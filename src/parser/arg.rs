use crate::lexer::kind::TokenKind;
use std::collections::{HashSet, VecDeque};
use std::fmt;

use crate::lexer::token::Token;
use crate::parser::error::ParseResult;
use crate::parser::program::Program;
use crate::parser::Type;

/// Represents a function argument declaration.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Argument {
    pub name: String,
    pub typ: Type,
}

impl fmt::Display for Argument {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.name.is_empty() {
            write!(f, "{}", self.typ)
        } else {
            write!(f, "{}: {}", self.name, self.typ)
        }
    }
}

impl Argument {
    pub fn new(name: &str, typ: Type) -> Self {
        Argument {
            name: name.to_string(),
            typ,
        }
    }

    /// Parses a function argument declaration. Expects token sequences of the form
    ///
    ///      <arg_name>: <arg_type>
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token should be the argument name.
        let name = Program::parse_identifier(tokens)?;

        // The next tokens should be a colon followed by the argument type.
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Colon]))?;
        let arg_type = Type::from(tokens)?;

        Ok(Argument::new(name.as_str(), arg_type))
    }

    /// Parses an unnamed function argument declaration. Expects token sequences of the form
    ///
    ///      <arg_type>
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    pub fn unnamed_from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The next token should be the argument type.
        let arg_type = Type::from(tokens)?;

        Ok(Argument::new("", arg_type))
    }
}
