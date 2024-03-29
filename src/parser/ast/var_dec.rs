use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::r#type::Type;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;
use std::hash::{Hash, Hasher};

/// Represents a variable declaration. Each variable declaration must have a valid type, a name,
/// and some value as the result of an expression.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDeclaration {
    pub maybe_type: Option<Type>,
    pub is_mut: bool,
    pub name: String,
    pub value: Expression,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Hash for VariableDeclaration {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.maybe_type.hash(state);
        self.is_mut.hash(state);
        self.name.hash(state);
        self.value.hash(state);
    }
}

locatable_impl!(VariableDeclaration);

impl VariableDeclaration {
    pub fn new(
        typ: Option<Type>,
        is_mut: bool,
        name: String,
        value: Expression,
        start_pos: Position,
        end_pos: Position,
    ) -> Self {
        VariableDeclaration {
            maybe_type: typ,
            is_mut,
            name,
            value,
            start_pos,
            end_pos,
        }
    }

    /// Parses variable declarations. Expects token sequences of the forms
    ///
    ///     let <name>: <type> = <expr>
    ///     let mut <name>: <type> = <expr>
    ///     let <name> = <expr>
    ///     let mut <name> = <expr>
    ///
    /// where
    ///  - `type` is the variable type
    ///  - `name` is the variable name
    ///  - `expr` is an expression representing the value assigned to the variable
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // The first token should be "let".
        let start_token = Module::parse_expecting(tokens, TokenKind::Let)?;

        // Parse the optional "mut".
        let is_mut = Module::parse_optional(tokens, TokenKind::Mut).is_some();

        // The second token should be the variable name.
        let name = Module::parse_identifier(tokens)?;

        // The colon and variable type are optional.
        let mut typ = None;
        if Module::parse_optional(tokens, TokenKind::Colon).is_some() {
            // There was a colon, so there should be a type name.
            typ = Some(Type::from(tokens)?);
        }

        // The remaining tokens should be "=" followed by the variable value.
        Module::parse_expecting(tokens, TokenKind::Equal)?;
        let value = Expression::from(tokens)?;
        let end_pos = value.end_pos().clone();

        Ok(VariableDeclaration::new(
            typ,
            is_mut,
            name,
            value,
            start_token.start,
            end_pos,
        ))
    }
}
