use std::collections::VecDeque;

use crate::lexer::token::Token;
use crate::parser::program::Program;
use crate::parser::{ParseResult, Type};

/// Represents a function argument declaration.
#[derive(Debug, PartialEq)]
pub struct Argument {
    name: String,
    typ: Type,
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
    ///      <arg_type> <arg_name>
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token should be the argument type.
        let arg_type = Type::from(tokens)?;

        // The second token should be the argument name.
        let name = Program::parse_identifier(tokens)?;

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
