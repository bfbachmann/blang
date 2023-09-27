use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use colored::Colorize;

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::expr::Expression;
use crate::parser::program::Program;
use crate::parser::r#type::Type;
use crate::parser::stream::Stream;
use crate::parser::unresolved::UnresolvedType;
use crate::util;

/// Represents a field in a struct with a type and a name.
#[derive(Debug, Clone, Eq)]
pub struct StructField {
    pub name: String,
    pub typ: Type,
    start_pos: Position,
    end_pos: Position,
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

impl Locatable for StructField {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

/// Represents a struct with a set of named fields.
#[derive(Debug, Clone, Eq)]
pub struct StructType {
    pub name: String,
    pub fields: Vec<StructField>,
    start_pos: Position,
    end_pos: Position,
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
        if self.name.is_empty() {
            write!(f, "struct {{ ... }}")
        } else {
            write!(f, "struct {} {{ ... }}", self.name)
        }
    }
}

impl PartialEq for StructType {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && util::vectors_are_equal(&self.fields, &other.fields)
    }
}

impl Locatable for StructType {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl StructType {
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
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Record the starting position of the struct type declaration.
        let start_pos = Program::current_position(tokens);
        let end_pos: Position;

        // The first token should be "struct".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Struct]))?;

        // The next token should might be the struct type name, which is optional.
        let mut name = "".to_string();
        if let Some(Token {
            kind: TokenKind::Identifier(_),
            ..
        }) = tokens.peek_next()
        {
            name = Program::parse_identifier(tokens)?;
        }

        // The next token should be `{`.
        Program::parse_expecting(tokens, HashSet::from([TokenKind::LeftBrace]))?;

        // Parse struct fields until we reach `}`.
        let mut fields = vec![];
        loop {
            // If the next token is `}`, we're done parsing the struct type declaration.
            if let Some(Token {
                kind: TokenKind::RightBrace,
                ..
            }) = tokens.peek_next()
            {
                // Record the position of the last token in the struct type declaration.
                let end_token = tokens.next().unwrap();
                end_pos = end_token.end;
                break;
            }

            // Get the field start position.
            let field_start_pos = Program::current_position(tokens);

            // The next token should be the field name.
            let field_name = Program::parse_identifier(tokens)?;

            // The next token should be a `:`.
            Program::parse_expecting(tokens, HashSet::from([TokenKind::Colon]))?;

            // The next tokens should represent the field type.
            let field_type = Type::from(tokens)?;

            // Get the field end position.
            // TODO: Technically, this is wrong.
            let field_end_pos = Program::current_position(tokens);

            // Parse the optional comma.
            Program::parse_optional(tokens, HashSet::from([TokenKind::Comma]));

            // Add the field to the map. We'll check for field name collisions in the analyzer.
            fields.push(StructField {
                name: field_name,
                typ: field_type,
                start_pos: field_start_pos,
                end_pos: field_end_pos,
            });
        }

        // Make sure to sort the fields by name so two equivalent struct types if different field
        // orders still look the same.
        fields.sort_by(|f1, f2| f1.name.cmp(&f2.name));
        Ok(StructType {
            name,
            fields,
            start_pos,
            end_pos,
        })
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
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Display for StructInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {{ ... }}", self.typ)
    }
}

impl PartialEq for StructInit {
    fn eq(&self, other: &Self) -> bool {
        self.typ == other.typ
            && util::hashmaps_are_equal(&self.field_values, &other.field_values)
            && self.start_pos == other.start_pos
            && self.end_pos == other.end_pos
    }
}

impl Locatable for StructInit {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
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
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Get the start position of the struct initialization in the source file.
        let start_pos = Program::current_position(tokens);
        let end_pos: Position;

        // Parse the struct type (either by name or inline declaration).
        let struct_type = match tokens.next() {
            Some(
                _token @ Token {
                    kind: TokenKind::Struct,
                    ..
                },
            ) => {
                tokens.rewind(1);
                Type::Struct(StructType::from(tokens)?)
            }

            Some(
                ref token @ Token {
                    kind: TokenKind::Identifier(ref type_name),
                    ..
                },
            ) => Type::Unresolved(UnresolvedType::new(
                type_name.as_str(),
                token.start,
                token.end,
            )),

            Some(other) => {
                return Err(ParseError::new(
                    ErrorKind::ExpectedType,
                    format_code!("expected struct type, but found {}", &other,).as_str(),
                    Some(other.clone()),
                    other.start,
                    other.end,
                ))
            }

            None => {
                return Err(ParseError::new(
                    ErrorKind::UnexpectedEOF,
                    "expected struct type, but found EOF",
                    None,
                    Position::default(),
                    Position::default(),
                ))
            }
        };

        // Parse `{`.
        Program::parse_expecting(tokens, HashSet::from([TokenKind::LeftBrace]))?;

        // Parse struct field assignments until we hit `}`.
        let mut field_values = HashMap::new();
        loop {
            match tokens.next() {
                Some(&Token {
                    kind: TokenKind::RightBrace,
                    ..
                }) => {
                    // Set the end position of this struct initialization in the source file.
                    end_pos = Program::current_position(tokens);
                    break;
                }

                Some(&Token {
                    kind: TokenKind::Identifier(ref field_name),
                    ..
                }) => {
                    // Parse `:` followed by the field value and record the field.
                    let field_name = field_name.clone();
                    Program::parse_expecting(tokens, HashSet::from([TokenKind::Colon]))?;
                    let value = Expression::from(tokens, false)?;
                    field_values.insert(field_name, value);

                    // Parse the optional comma.
                    Program::parse_optional(tokens, HashSet::from([TokenKind::Comma]));
                }

                Some(other) => {
                    return Err(ParseError::new(
                        ErrorKind::UnexpectedEndOfExpr,
                        "expected struct field assignment or }",
                        Some(other.clone()),
                        other.start,
                        other.end,
                    ))
                }

                None => {
                    return Err(ParseError::new(
                        ErrorKind::UnexpectedEOF,
                        "expected struct field assignment or }, but found EOF",
                        None,
                        Position::default(),
                        Position::default(),
                    ))
                }
            }
        }

        Ok(StructInit {
            typ: struct_type,
            field_values,
            start_pos,
            end_pos,
        })
    }
}
