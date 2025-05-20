use std::fmt;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Position, Span};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::params::Params;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::symbol::{Name, Symbol};
use crate::parser::ast::unresolved::UnresolvedType;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a field in a struct with a type and a name.
#[derive(Debug, Clone, Eq)]
pub struct StructField {
    pub name: String,
    pub typ: Type,
    pub is_pub: bool,
    pub span: Span,
}

impl PartialEq for StructField {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.typ == other.typ
    }
}

impl Hash for StructField {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.typ.hash(state);
    }
}

locatable_impl!(StructField);

/// Represents a struct with a set of named fields.
#[derive(Debug, Clone, Eq)]
pub struct StructType {
    pub name: Name,
    pub maybe_params: Option<Params>,
    pub fields: Vec<StructField>,
    pub is_pub: bool,
    pub span: Span,
}

impl Hash for StructType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        for field in &self.fields {
            field.hash(state);
        }
    }
}

impl Display for StructType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.name.value.is_empty() {
            write!(f, "struct {{ ... }}")
        } else {
            write!(f, "struct {} {{ ... }}", self.name)
        }
    }
}

impl PartialEq for StructType {
    fn eq(&self, other: &Self) -> bool {
        if self.name != other.name
            || self.fields.len() != other.fields.len()
            || self.is_pub != other.is_pub
        {
            return false;
        }

        if self.maybe_params != other.maybe_params {
            return false;
        }

        for field in &self.fields {
            if !other.fields.iter().any(|f| f == field) {
                return false;
            }
        }

        true
    }
}

locatable_impl!(StructType);

impl StructType {
    /// Parses a struct declaration. Expects token sequences of the form
    ///
    ///     pub struct <name><params> {
    ///         <field>: <type>,
    ///         ...
    ///     }
    ///
    /// where
    ///  - `name` is the struct type name
    ///  - `params` are generic parameters (optional)
    ///  - `type` is the struct field type
    ///  - `field` is the struct field name
    ///  - `pub` is optional
    ///
    /// The commas after each field declaration are optional.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        let is_pub = parser.parse_optional(TokenKind::Pub).is_some();

        // Record the starting position of the struct type declaration.
        let start_pos = parser.current_position();
        let end_pos: Position;

        // The first token should be `struct`.
        parser.parse_expecting(TokenKind::Struct)?;

        // The next token is the struct type name.
        let name = Name::parse(parser)?;

        // Parse optional generic parameters.
        let maybe_params = match parser.next_token_is(&TokenKind::LeftBracket) {
            true => Some(Params::parse(parser)?),
            false => None,
        };

        // The next token should be `{`.
        parser.parse_expecting(TokenKind::LeftBrace)?;

        // Parse struct fields until we reach `}`.
        let mut fields = vec![];
        loop {
            // If the next token is `}`, we're done parsing the struct type declaration.
            if let Some(Token {
                kind: TokenKind::RightBrace,
                ..
            }) = parser.tokens.peek_next()
            {
                // Record the position of the last token in the struct type declaration.
                let end_token = parser.tokens.next().unwrap();
                end_pos = end_token.span.end_pos;
                break;
            }

            // Get the field start position.
            let field_start_pos = parser.current_position();

            // Parse the optional `pub` keyword.
            let is_pub = parser.parse_optional(TokenKind::Pub).is_some();

            // The next token should be the field name.
            let field_name = parser.parse_identifier()?;

            // The next token should be a `:`.
            parser.parse_expecting(TokenKind::Colon)?;

            // The next tokens should represent the field type.
            let field_type = Type::parse(parser)?;

            // Get the field end position.
            let field_end_pos = parser.prev_position();

            // Parse the optional comma.
            parser.parse_optional(TokenKind::Comma);

            // Add the field to the map. We'll check for field name collisions in the analyzer.
            fields.push(StructField {
                name: field_name,
                typ: field_type,
                is_pub,
                span: parser.new_span(field_start_pos, field_end_pos),
            });
        }

        Ok(StructType {
            name,
            maybe_params,
            fields,
            is_pub,
            span: parser.new_span(start_pos, end_pos),
        })
    }
}

/// Represents struct initialization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructInit {
    pub typ: UnresolvedType,
    /// Maps struct field name to the value assigned to it.
    pub field_values: Vec<(Symbol, Expression)>,
    pub span: Span,
}

impl Display for StructInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {{ ... }}", self.typ)
    }
}

impl Hash for StructInit {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.typ.hash(state);
        self.field_values.hash(state);
    }
}

locatable_impl!(StructInit);

impl StructInit {
    /// Parses struct initialization. Expects token sequences of the form
    ///
    ///     <type> {
    ///         <field>: <value>,
    ///         ...
    ///     }
    ///
    /// where
    ///  - `type` is the unresolved struct type
    ///  - `field` is the struct field name
    ///  - `value` is the value being assigned to the field
    ///
    /// The commas after each field assignment are optional.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        // Get the start position of the struct initialization in the source file.
        let start_pos = parser.current_position();
        let end_pos: Position;

        // Parse the struct type symbol.
        let typ = UnresolvedType::from_symbol(Symbol::parse(parser)?);

        // Parse `{`.
        parser.parse_expecting(TokenKind::LeftBrace)?;

        // Parse struct field assignments until we hit `}`.
        let mut field_values = vec![];
        loop {
            match parser.tokens.next() {
                Some(&Token {
                    kind: TokenKind::RightBrace,
                    ..
                }) => {
                    // Set the end position of this struct initialization in the source file.
                    end_pos = parser.prev_position();
                    break;
                }

                Some(&Token {
                    kind: TokenKind::Identifier(_),
                    ..
                }) => {
                    // Parse `:` followed by the field value and record the field.
                    parser.tokens.rewind(1);
                    let field_name = Symbol::parse_as_identifier(parser)?;
                    parser.parse_expecting(TokenKind::Colon)?;
                    let value = Expression::parse(parser)?;
                    field_values.push((field_name, value));

                    // Parse the optional comma.
                    parser.parse_optional(TokenKind::Comma);
                }

                Some(other) => {
                    return Err(ParseError::new(
                        ErrorKind::UnexpectedEndOfExpr,
                        "expected struct field assignment or }",
                        Some(other.clone()),
                        other.span,
                    ))
                }

                None => {
                    return Err(ParseError::new(
                        ErrorKind::UnexpectedEOF,
                        "expected struct field assignment or }, but found EOF",
                        None,
                        Default::default(),
                    ))
                }
            }
        }

        Ok(StructInit {
            typ,
            field_values,
            span: parser.new_span(start_pos, end_pos),
        })
    }
}
