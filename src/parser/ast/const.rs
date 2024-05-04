use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::r#type::Type;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;
use crate::{locatable_impl, util};

/// Represents a single module-level constant declaration.
#[derive(Debug, Eq, Clone)]
pub struct Const {
    pub name: String,
    pub maybe_type: Option<Type>,
    pub value: Expression,
    pub is_pub: bool,
    start_pos: Position,
    end_pos: Position,
}

impl Hash for Const {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.maybe_type.hash(state);
        self.value.hash(state);
    }
}

impl PartialEq for Const {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && util::opts_eq(&self.maybe_type, &other.maybe_type)
            && self.value == other.value
    }
}

impl Display for Const {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;

        if let Some(typ) = &self.maybe_type {
            write!(f, ": {}", typ)?;
        }

        write!(f, " = {}", self.value)
    }
}

locatable_impl!(Const);

impl Const {
    /// Parses a single constant declaration from the token stream. Expects token sequences of the
    /// forms
    ///
    ///     pub const <name>: <type> = <value>
    ///     pub const <name> = <value>
    ///
    /// where
    ///  - `name` is an identifier representing the constant name
    ///  - `type` is the optional constant type (see `Type::from`)
    ///  - `value` is an expression representing the constant value (see `Expression::from`)
    ///  - `pub` is optional.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let is_pub = Module::parse_optional(tokens, TokenKind::Pub).is_some();
        let start_pos = Module::parse_expecting(tokens, TokenKind::Const)?.start;
        let name = Module::parse_identifier(tokens)?;

        // Parse the optional `: <type>`.
        let typ = match Module::parse_optional(tokens, TokenKind::Colon) {
            Some(_) => Some(Type::from(tokens)?),
            None => None,
        };

        // The next token should be `=`.
        Module::parse_expecting(tokens, TokenKind::Equal)?;

        // Parse the value as an expression and compute the end position of the statement.
        let value = Expression::from(tokens)?;
        let end_pos = value.end_pos().clone();

        Ok(Const {
            name,
            maybe_type: typ,
            value,
            is_pub,
            start_pos,
            end_pos,
        })
    }
}
