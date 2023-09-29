use std::fmt::{Display, Formatter};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::error::ParseResult;
use crate::parser::expr::Expression;
use crate::parser::program::Program;
use crate::parser::r#type::Type;
use crate::parser::stream::Stream;
use crate::util;

/// Represents a single module-level constant declaration.
#[derive(Debug, Clone)]
pub struct Const {
    pub name: String,
    pub typ: Option<Type>,
    pub value: Expression,
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for Const {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && util::optionals_are_equal(&self.typ, &other.typ)
            && self.value == other.value
    }
}

impl Display for Const {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;

        if let Some(typ) = &self.typ {
            write!(f, ": {}", typ)?;
        }

        write!(f, " = {}", self.value)
    }
}

impl Locatable for Const {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl Const {
    /// Parses a single constant declaration from the token stream. Expects token sequences of the
    /// forms
    ///
    ///     <name>: <type> = <value>
    ///     <name> = <value>
    ///
    /// where
    ///  - `name` is an identifier representing the constant name
    ///  - `type` is the optional constant type (see `Type::from`)
    ///  - `value` is an expression representing the constant value (see `Expression::from`).
    fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let start_pos = Program::current_position(tokens);
        let name = Program::parse_identifier(tokens)?;

        // Parse the optional `: <type>`.
        let typ = match Program::parse_optional(tokens, TokenKind::Colon) {
            Some(_) => Some(Type::from(tokens)?),
            None => None,
        };

        // The next token should be `=`.
        Program::parse_expecting(tokens, TokenKind::Equal)?;

        // Parse the value as an expression and compute the end position of the statement.
        let value = Expression::from(tokens, false)?;
        let end_pos = value.end_pos().clone();

        Ok(Const {
            name,
            typ,
            value,
            start_pos,
            end_pos,
        })
    }
}

/// Represents a `const` statement that declares a set of module-level constants.
#[derive(Debug, PartialEq)]
pub struct ConstBlock {
    pub consts: Vec<Const>,
    start_pos: Position,
    end_pos: Position,
}

impl Clone for ConstBlock {
    fn clone(&self) -> Self {
        ConstBlock {
            consts: self.consts.iter().map(|c| c.clone()).collect(),
            start_pos: self.start_pos.clone(),
            end_pos: self.end_pos.clone(),
        }
    }
}

impl Display for ConstBlock {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.consts.len() == 1 {
            write!(f, "{}", self.consts.first().unwrap())
        } else {
            write!(f, "const {{ <{} const declarations> }}", self.consts.len())
        }
    }
}

impl Locatable for ConstBlock {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl ConstBlock {
    /// Parses a `const` statement from the given token sequence. Expects token sequences of the
    /// forms
    ///
    ///     const <name>: <type> = <value>
    ///     const <name> = <value>
    ///     const { ... }
    ///
    /// where
    ///  - `name` is an identifier representing the constant name
    ///  - `type` is the optional constant type (see `Type::from`)
    ///  - `value` is an expression representing the constant value (see `Expression::from`).
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Get the start position of the statement.
        let start_pos = Program::current_position(tokens);

        // The first token should be `const`.
        Program::parse_expecting(tokens, TokenKind::Const)?;

        // The second token should be an identifier or `{`.
        let mut consts = vec![];
        let end_pos;
        if Program::parse_optional(tokens, TokenKind::LeftBrace).is_some() {
            // This is a constant block. We need to parse all the constant declarations contained
            // within it until we reach the closing `}`.
            loop {
                if let Some(token) = Program::parse_optional(tokens, TokenKind::RightBrace) {
                    end_pos = token.end;
                    break;
                }

                consts.push(Const::from(tokens)?);
            }
        } else {
            // This is just a single constant declaration.
            let const_decl = Const::from(tokens)?;
            end_pos = const_decl.end_pos.clone();
            consts.push(const_decl);
        }

        Ok(ConstBlock {
            consts,
            start_pos,
            end_pos,
        })
    }
}