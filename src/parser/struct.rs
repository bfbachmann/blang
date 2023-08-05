use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::fmt::{Display, Formatter};

use crate::lexer::kind::TokenKind;
use crate::lexer::token::Token;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::expr::Expression;
use crate::parser::program::Program;
use crate::parser::r#type::Type;
use crate::parser::ParseResult;
use crate::util;

/// Represents a field in a struct with a type and a name.
#[derive(Debug, PartialEq, Clone)]
pub struct StructField {
    pub name: String,
    pub typ: Type,
}

/// Represents a struct with a set of named fields.
#[derive(Debug, Clone)]
pub struct Struct {
    pub name: String,
    pub fields: Vec<StructField>,
}

impl fmt::Display for Struct {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "struct {} {{ ... }}", self.name)
    }
}

impl PartialEq for Struct {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && util::vectors_are_equal(&self.fields, &other.fields)
    }
}

impl Struct {
    /// Parses a struct declaration. Expects token sequences of the form
    ///
    ///     struct <name> {
    ///         <field>: <type>,
    ///         ...
    ///     }
    ///
    /// where
    ///  - `name` is the struct type name (optional)
    ///  - `type` is the struct field type
    ///  - `field` is the struct field name
    ///
    /// The commas after each field declaration are optional.
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token should be "struct".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Struct]))?;

        // The next token should might be the struct type name, which is optional.
        let mut name = "".to_string();
        if let Some(Token {
            kind: TokenKind::Identifier(_),
            ..
        }) = tokens.front()
        {
            name = Program::parse_identifier(tokens)?;
        }

        // The next token should be "{".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::BeginClosure]))?;

        // Parse struct fields until we reach "}".
        let mut fields = vec![];
        loop {
            // If the next token is "}", we're done parsing the struct type declaration.
            if let Some(Token {
                kind: TokenKind::EndClosure,
                ..
            }) = tokens.front()
            {
                tokens.pop_front();
                break;
            }

            // The next token should be the field name.
            let field_name = Program::parse_identifier(tokens)?;

            // The next token should be a ":".
            Program::parse_expecting(tokens, HashSet::from([TokenKind::Colon]))?;

            // The next tokens should represent the field type.
            let field_type = Type::from(tokens)?;

            // Parse the optional comma.
            Program::parse_optional(tokens, HashSet::from([TokenKind::Comma]));

            // Add the field to the map. We'll check for field name collisions in the analyzer.
            fields.push(StructField {
                name: field_name,
                typ: field_type,
            });
        }

        Ok(Struct { name, fields })
    }
}

/// Represents struct initialization.
#[derive(Debug, Clone)]
pub struct StructInit {
    /// Type should only ever be `Type::Unresolved` (for named struct types) or `Type::Struct` (for
    /// struct types defined inline).
    pub typ: Type,
    /// Maps struct field name to the value assigned to it.
    pub field_values: HashMap<String, Expression>,
}

impl Display for StructInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {{ ... }}", self.typ)
    }
}

impl PartialEq for StructInit {
    fn eq(&self, other: &Self) -> bool {
        self.typ == other.typ && util::hashmaps_are_equal(&self.field_values, &other.field_values)
    }
}

impl StructInit {
    /// Parses struct initialization. Expects token sequences of the form
    ///
    ///     <name> {
    ///         <field>: <value>,
    ///         ...
    ///     }
    ///
    /// where
    ///  - `name` is the struct type name
    ///  - `field` is the struct field name
    ///  - `value` is the value being assigned to the field
    ///
    /// The commas after each field assignment are optional.
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // Parse the struct type (either by name or inline declaration).
        let struct_type = match tokens.pop_front() {
            Some(
                token @ Token {
                    kind: TokenKind::Struct,
                    ..
                },
            ) => {
                tokens.push_front(token);
                Type::Struct(Struct::from(tokens)?)
            }
            Some(Token {
                kind: TokenKind::Identifier(type_name),
                ..
            }) => Type::Unresolved(type_name),
            other => {
                return Err(ParseError::new(
                    ErrorKind::ExpectedType,
                    "expected struct type",
                    other,
                ))
            }
        };

        // Parse "{".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::BeginClosure]))?;

        // Parse struct field assignments until we hit "}".
        let mut field_values = HashMap::new();
        loop {
            match tokens.pop_front() {
                Some(Token {
                    kind: TokenKind::EndClosure,
                    ..
                }) => break,

                Some(Token {
                    kind: TokenKind::Identifier(field_name),
                    ..
                }) => {
                    // Parse ":" followed by the field value and record the field.
                    Program::parse_expecting(tokens, HashSet::from([TokenKind::Colon]))?;
                    let value = Expression::from(tokens, false, false)?;
                    field_values.insert(field_name, value);

                    // Parse the optional comma.
                    Program::parse_optional(tokens, HashSet::from([TokenKind::Comma]));
                }

                other => {
                    return Err(ParseError::new(
                        ErrorKind::UnexpectedEndOfExpr,
                        "expected struct field assignment or }",
                        other,
                    ))
                }
            }
        }

        Ok(StructInit {
            typ: struct_type,
            field_values,
        })
    }
}
