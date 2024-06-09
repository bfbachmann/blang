use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::symbol::Symbol;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

/// Represents a generic compile-time parameter. A parameter has a name and has
/// a set of associated specs that any type used in its place must implement.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Param {
    /// The name given to the parameter.
    pub name: String,
    /// The specs that this parameter requires.
    pub required_specs: Vec<Symbol>,
    span: Span,
}

impl Hash for Param {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);

        for spec in &self.required_specs {
            spec.hash(state);
        }
    }
}

impl Param {
    /// Parses a parameter. Expects token sequences of the forms
    ///
    ///     <name>: <spec> + ...
    ///
    /// where
    ///  - `name` is an identifier representing the parameter name
    ///  - `spec` is any spec that a type satisfying the requirements must implement. Note that the
    ///    specs are being parsed as types, because specs and types are represented the same way.
    ///    The set of specs may be empty.
    ///
    /// In the first example, one or more specs are provided. Only types that implement all of these
    /// specs can satisfy the parameter's requirements.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Find the start position and (maybe) the end position of this param.
        let span = match tokens.peek_next() {
            Some(token) => token.span,
            None => Default::default(),
        };

        // Parse the param name.
        let mut param = Param {
            name: Module::parse_identifier(tokens)?,
            required_specs: vec![],
            span,
        };

        // Parse the optional `: <spec> + ...`.
        if Module::parse_optional(tokens, TokenKind::Colon).is_some() {
            loop {
                let spec = Symbol::from(tokens)?;
                param.required_specs.push(spec);

                // Stop parsing specs if the next token is not a `+`.
                if Module::parse_optional(tokens, TokenKind::Plus).is_none() {
                    param.span.end_pos = param.required_specs.last().unwrap().span.end_pos;
                    break;
                }
            }
        }

        Ok(param)
    }

    /// Creates a new param with default start and end positions
    pub fn new_with_default_pos(name: &str) -> Self {
        Param {
            name: name.to_string(),
            required_specs: vec![],
            span: Default::default(),
        }
    }
}

locatable_impl!(Param);

/// Represents generic parameters. A set of generic parameters is just a set of
/// types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Params {
    pub params: Vec<Param>,
    span: Span,
}

impl Hash for Params {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for param in &self.params {
            param.hash(state);
        }
    }
}

locatable_impl!(Params);

impl Params {
    /// Parses a set of parameters. Expects token sequences of the forms
    ///
    ///     [<param>,...]
    ///
    /// where
    ///  - `param` is a generic parameter (see `Param::from`).
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Parse `[`.
        let start_pos = Module::parse_expecting(tokens, TokenKind::LeftBracket)?
            .span
            .start_pos;

        // Parse all params and the closing bracket.
        let mut params = vec![];
        let end_pos = loop {
            // Parse the param (there must be at least one).
            params.push(Param::from(tokens)?);

            // The next token should either be a comma or the closing bracket.
            match Module::parse_expecting_any(
                tokens,
                vec![TokenKind::Comma, TokenKind::RightBracket],
            )? {
                Token {
                    kind: TokenKind::RightBracket,
                    span,
                    ..
                } => {
                    break span.end_pos;
                }

                _ => {
                    // Allow trailing commas.
                    if let Some(token) = Module::parse_optional(tokens, TokenKind::RightBracket) {
                        break token.span.end_pos;
                    }
                }
            };
        };

        Ok(Params {
            params,
            span: Span { start_pos, end_pos },
        })
    }

    /// Creates a new set of generic params with default (zero) start and end position.
    pub fn new_with_default_pos() -> Self {
        Params {
            params: vec![],
            span: Default::default(),
        }
    }
}
