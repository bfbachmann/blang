use std::fmt;

use crate::lexer::pos::Span;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::pointer::PointerType;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::unresolved::UnresolvedType;
use crate::parser::error::{ErrorKind, ParseError, ParseResult};
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a function argument declaration.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Argument {
    pub name: String,
    pub typ: Type,
    pub is_mut: bool,
    pub span: Span,
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
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        // Get the argument starting position in the source code.
        let start_pos = parser.current_position();

        // Handle the special cases of `*self` and `*mut self`.
        if parser.parse_optional(TokenKind::Asterisk).is_some() {
            let is_mut = parser.parse_optional(TokenKind::Mut).is_some();
            let name = parser.parse_identifier()?;
            if name != "self" {
                return Err(ParseError::new_with_token(
                    ErrorKind::ExpectedIdent,
                    format_code!("expected {}, but found {}", "self", name).as_str(),
                    parser.tokens.prev().unwrap().clone(),
                ));
            }

            let end_pos = parser.prev_position();

            return Ok(Argument::new(
                name.as_str(),
                Type::Pointer(Box::new(PointerType::new(
                    Type::Unresolved(UnresolvedType::new(
                        "Self",
                        parser.new_span(start_pos, parser.prev_position()),
                    )),
                    is_mut,
                    parser.new_span(start_pos, end_pos),
                ))),
                is_mut,
                parser.new_span(start_pos, end_pos),
            ));
        }

        // The argument can optionally be declared as mutable, so check for "mut".
        let is_mut = parser.parse_optional(TokenKind::Mut).is_some();

        // The first token should be the argument name.
        let mut end_pos = parser.current_position();
        let name = parser.parse_identifier()?;
        end_pos.col += name.len() as u32;

        // If the argument name is `self`, it doesn't need a type. Otherwise, it's a regular
        // argument with a type.
        if name == "self" {
            return Ok(Argument::new(
                name.as_str(),
                Type::Unresolved(UnresolvedType::new(
                    "Self",
                    parser.new_span(start_pos, parser.prev_position()),
                )),
                is_mut,
                parser.new_span(start_pos, end_pos),
            ));
        }

        // The next token should be a colon.
        parser.parse_expecting(TokenKind::Colon)?;

        // The remaining tokens should form the argument type.
        let arg_type = Type::parse(parser)?;

        // Get the argument ending position in the source code.
        let end_pos = arg_type.span().end_pos;

        Ok(Argument::new(
            name.as_str(),
            arg_type,
            is_mut,
            parser.new_span(start_pos, end_pos),
        ))
    }

    /// Parses an unnamed function argument declaration. Expects token sequences of the forms
    ///
    ///      <arg_type>
    ///      mut <arg_type>
    ///
    /// where
    ///  - `arg_type` is the type of the argument
    pub fn parse_unnamed(parser: &mut FileParser) -> ParseResult<Self> {
        // Get the argument starting position in the source code.
        let start_pos = parser.current_position();

        // Check for the optional "mut" keyword for mutable arguments.
        let is_mut = parser.parse_optional(TokenKind::Mut).is_some();

        // The next token should be the argument type.
        let arg_type = Type::parse(parser)?;

        // Get the argument ending position in the source code.
        let end_pos = arg_type.span().end_pos;

        Ok(Argument::new(
            "",
            arg_type,
            is_mut,
            parser.new_span(start_pos, end_pos),
        ))
    }
}
