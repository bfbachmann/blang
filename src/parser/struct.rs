use std::collections::{HashSet, VecDeque};
use std::fmt;
use std::fmt::Formatter;

use crate::lexer::kind::TokenKind;
use crate::lexer::token::Token;
use crate::parser::error::{ErrorKind, ParseError};

use crate::parser::func_sig::FunctionSignature;
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
    ///         <type> <field>
    ///         ...
    ///     }
    ///
    /// where
    ///  - `name` is the struct type name
    ///  - `type` is the struct field type
    ///  - `field` is the struct field name
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
            // The next token should either be the field type name or "}".
            let field_type = match tokens.pop_front() {
                Some(Token {
                    kind: TokenKind::EndClosure,
                    ..
                }) => {
                    // We've reached the end of the struct declaration, so we're done!
                    break;
                }

                Some(Token {
                    kind: TokenKind::I64,
                    ..
                }) => Type::I64,

                Some(Token {
                    kind: TokenKind::Bool,
                    ..
                }) => Type::Bool,

                Some(Token {
                    kind: TokenKind::String,
                    ..
                }) => Type::String,

                Some(Token {
                    kind: TokenKind::Identifier(type_name),
                    ..
                }) => Type::Unresolved(type_name),

                Some(
                    token @ Token {
                        kind: TokenKind::Function,
                        ..
                    },
                ) => {
                    tokens.push_front(token);
                    let fn_sig = FunctionSignature::from_anon(tokens, false)?;
                    Type::Function(Box::new(fn_sig))
                }

                Some(
                    token @ Token {
                        kind: TokenKind::Struct,
                        ..
                    },
                ) => {
                    tokens.push_front(token);
                    let struct_type = Struct::from(tokens)?;
                    Type::Struct(struct_type)
                }

                other => {
                    return Err(ParseError::new(
                        ErrorKind::ExpectedType,
                        "expected struct field type",
                        other,
                    ))
                }
            };

            // The next token should be the field name.
            let field_name = Program::parse_identifier(tokens)?;

            // Add the field to the map. We'll check for field name collisions in the analyzer.
            fields.push(StructField {
                name: field_name,
                typ: field_type,
            });
        }

        Ok(Struct { name, fields })
    }
}
