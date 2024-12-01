use std::fmt;

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::pointer::PointerType;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::unresolved::UnresolvedType;
use crate::parser::error::{ErrorKind, ParseError, ParseResult};
use crate::parser::module::Module;

/// Represents a function argument declaration.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Argument {
    pub name: String,
    pub typ: Type,
    pub is_mut: bool,
    span: Span,
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

locatable_impl!(Argument);

impl Argument {
    /// Creates a new function argument.
    pub fn new(name: &str, typ: Type, is_mut: bool, span: Span) -> Self {
        Argument {
            name: name.to_string(),
            typ,
            is_mut,
            span,
        }
    }

    /// Creates a new function argument with default (zero) start and end positions.
    #[cfg(test)]
    pub fn new_with_default_pos(name: &str, typ: Type, is_mut: bool) -> Self {
        Argument {
            name: name.to_string(),
            typ,
            is_mut,
            span: Default::default(),
        }
    }

    /// Parses a function argument declaration. Expects token sequences of the forms
    ///
    ///     <arg_name>: <arg_type>
    ///     mut <arg_name>: <arg_type>
    ///     self
    ///     *self
    ///     mut self
    ///     *mut self
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    ///  - `arg_name` is an identifier representing the argument name
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Get the argument starting position in the source code.
        let start_pos = Module::current_position(tokens);

        // Handle the special cases of `*self` and `*mut self`.
        if Module::parse_optional(tokens, TokenKind::Asterisk).is_some() {
            let is_mut = Module::parse_optional(tokens, TokenKind::Mut).is_some();
            let name = Module::parse_identifier(tokens)?;
            if name != "self" {
                return Err(ParseError::new_with_token(
                    ErrorKind::ExpectedIdent,
                    format_code!("expected {}, but found {}", "self", name).as_str(),
                    tokens.prev().unwrap().clone(),
                ));
            }

            let end_pos = Module::prev_position(tokens);

            return Ok(Argument::new(
                name.as_str(),
                Type::Pointer(Box::new(PointerType::new(
                    Type::Unresolved(UnresolvedType::new(
                        "Self",
                        Span {
                            start_pos,
                            end_pos: Module::prev_position(tokens),
                        },
                    )),
                    is_mut,
                    Span { start_pos, end_pos },
                ))),
                is_mut,
                Span { start_pos, end_pos },
            ));
        }

        // The argument can optionally be declared as mutable, so check for "mut".
        let is_mut = Module::parse_optional(tokens, TokenKind::Mut).is_some();

        // The first token should be the argument name.
        let mut end_pos = Module::current_position(tokens);
        let name = Module::parse_identifier(tokens)?;
        end_pos.col += name.len();

        // If the argument name is `self`, it doesn't need a type. Otherwise, it's a regular
        // argument with a type.
        if name == "self" {
            return Ok(Argument::new(
                name.as_str(),
                Type::Unresolved(UnresolvedType::new(
                    "Self",
                    Span {
                        start_pos,
                        end_pos: Module::prev_position(tokens),
                    },
                )),
                is_mut,
                Span { start_pos, end_pos },
            ));
        }

        // The next token should be a colon.
        Module::parse_expecting(tokens, TokenKind::Colon)?;

        // The remaining tokens should form the argument type.
        let arg_type = Type::from(tokens)?;

        // Get the argument ending position in the source code.
        let end_pos = arg_type.end_pos().clone();

        Ok(Argument::new(
            name.as_str(),
            arg_type,
            is_mut,
            Span { start_pos, end_pos },
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
        let start_pos = Module::current_position(tokens);

        // Check for the optional "mut" keyword for mutable arguments.
        let is_mut = Module::parse_optional(tokens, TokenKind::Mut).is_some();

        // The next token should be the argument type.
        let arg_type = Type::from(tokens)?;

        // Get the argument ending position in the source code.
        let end_pos = arg_type.end_pos().clone();

        Ok(Argument::new(
            "",
            arg_type,
            is_mut,
            Span { start_pos, end_pos },
        ))
    }
}
