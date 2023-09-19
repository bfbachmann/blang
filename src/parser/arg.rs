use std::collections::HashSet;
use std::fmt;

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::error::ParseResult;
use crate::parser::program::Program;
use crate::parser::stream::Stream;
use crate::parser::Type;

/// Represents a function argument declaration.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Argument {
    pub name: String,
    pub typ: Type,
    pub is_mut: bool,
    start_pos: Position,
    end_pos: Position,
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

impl Locatable for Argument {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl Argument {
    /// Creates a new function argument.
    pub fn new(
        name: &str,
        typ: Type,
        is_mut: bool,
        start_pos: Position,
        end_pos: Position,
    ) -> Self {
        Argument {
            name: name.to_string(),
            typ,
            is_mut,
            start_pos,
            end_pos,
        }
    }

    /// Creates a new function argument with default (zero) start and end positions.
    pub fn new_with_default_pos(name: &str, typ: Type, is_mut: bool) -> Self {
        Argument {
            name: name.to_string(),
            typ,
            is_mut,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Parses a function argument declaration. Expects token sequences of the forms
    ///
    ///      <arg_name>: <arg_type>
    ///      <arg_name>: mut <arg_type>
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Get the argument starting position in the source code.
        let start_pos = Program::current_position(tokens);

        // The first token should be the argument name.
        let name = Program::parse_identifier(tokens)?;

        // The next token should be a colon.
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Colon]))?;

        // Check for the optional "mut" keyword for mutable arguments.
        let is_mut = Program::parse_optional(tokens, HashSet::from([TokenKind::Mut])).is_some();

        // The remaining tokens should form the argument type.
        let arg_type = Type::from(tokens)?;

        // Get the argument ending position in the source code.
        let end_pos = arg_type.end_pos().clone();

        Ok(Argument::new(
            name.as_str(),
            arg_type,
            is_mut,
            start_pos,
            end_pos,
        ))
    }

    /// Parses an unnamed function argument declaration. Expects token sequences of the forms
    ///
    ///      <arg_type>
    ///      mut <arg_type>
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    pub fn unnamed_from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Get the argument starting position in the source code.
        let start_pos = Program::current_position(tokens);

        // Check for the optional "mut" keyword for mutable arguments.
        let is_mut = Program::parse_optional(tokens, HashSet::from([TokenKind::Mut])).is_some();

        // The next token should be the argument type.
        let arg_type = Type::from(tokens)?;

        // Get the argument ending position in the source code.
        let end_pos = arg_type.end_pos().clone();

        Ok(Argument::new("", arg_type, is_mut, start_pos, end_pos))
    }
}
