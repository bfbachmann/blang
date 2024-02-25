use std::collections::HashSet;
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::r#type::Type;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

/// Represents a template parameter. A template parameter has a name and has either one associated
/// type, a set of associated specs, or no associated type or specs (i.e. is a wildcard parameter).
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TmplParam {
    /// The name given to the template parameter.
    pub name: String,
    /// The specs that this template parameter requires.
    pub required_specs: Vec<Type>,
    /// The type that this template parameter is an alias for.
    pub aliased_type: Option<Type>,
    start_pos: Position,
    end_pos: Position,
}

impl Hash for TmplParam {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);

        for spec in &self.required_specs {
            spec.hash(state);
        }

        if let Some(typ) = &self.aliased_type {
            typ.hash(state);
        }
    }
}

impl TmplParam {
    /// Parses a template parameter. Expects token sequences of the forms
    ///
    ///     <name>
    ///     <name> = <type>
    ///     <name>: <spec> +...
    ///
    /// where
    ///  - `name` is an identifier representing the template parameter name
    ///  - `type` is the type that satisfies the parameter requirement (see `Type::from`)
    ///  - `spec` is any spec that a type satisfying the requirements must implement. Note that the
    ///    specs are being parsed as types, because specs and types are represented the same way.
    ///
    /// In the first example above, only a parameter name is provided with no requirements. Any
    /// type can satisfy this parameter's requirements.
    /// In the second example, a type is provided. Only that type may be used in place of the
    /// corresponding parameter.
    /// In the last example, one or more specs are provided. Only types that implement all of these
    /// specs can satisfy the parameter's requirements.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Find the start position and (maybe) the end position of this template param.
        let (start_pos, end_pos) = match tokens.peek_next() {
            Some(token) => (token.start, token.end),
            None => (Position::default(), Position::default()),
        };

        // Parse the template param name.
        let mut tmpl_param = TmplParam {
            name: Module::parse_identifier(tokens)?,
            required_specs: vec![],
            aliased_type: None,
            start_pos,
            end_pos,
        };

        // Parse the type or spec requirements based on whether the next token is `=`, `:`, or
        // something else.
        match tokens.peek_next() {
            Some(Token {
                kind: TokenKind::Equal,
                ..
            }) => {
                tokens.next();
                tmpl_param.aliased_type = Some(Type::from(tokens)?);
            }

            Some(Token {
                kind: TokenKind::Colon,
                ..
            }) => {
                tokens.next();
                loop {
                    // We can safely use `Type::from` here because specs are always referenced by
                    // name and therefor parse cleanly as unresolved types. The analyzer will
                    // figure out if these are types or specs.
                    let spec = Type::from(tokens)?;
                    tmpl_param.required_specs.push(spec);

                    // Stop parsing types/specs if the next token is not a comma.
                    if Module::parse_optional(tokens, TokenKind::Plus).is_none() {
                        break;
                    }
                }

                // Fix the end position since we found parameter requirements.
                tmpl_param.end_pos = tmpl_param.required_specs.last().unwrap().end_pos().clone();
            }

            _ => {}
        };

        Ok(tmpl_param)
    }

    /// Creates a new template param with default start and end positions
    pub fn new_with_default_pos(name: &str) -> Self {
        TmplParam {
            name: name.to_string(),
            required_specs: vec![],
            aliased_type: None,
            start_pos: Default::default(),
            end_pos: Default::default(),
        }
    }
}

locatable_impl!(TmplParam);

/// Represents template parameters. A set of template parameters is just a set of generic types,
/// each with an optional set of specs that the type implements, or a single concrete type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TmplParams {
    pub params: Vec<TmplParam>,
    start_pos: Position,
    end_pos: Position,
}

impl Hash for TmplParams {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for param in &self.params {
            param.hash(state);
        }
    }
}

locatable_impl!(TmplParams);

impl TmplParams {
    /// Parses a set of template parameters. Expects token sequences of the forms
    ///
    ///     with [<type_param>,...]
    ///
    /// where
    ///  - `tmpl_param` is a template parameter (see `TmplParam::from`).
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Parse `with [`.
        let start_pos = Module::parse_expecting(tokens, TokenKind::With)?.start;
        Module::parse_expecting(tokens, TokenKind::LeftBracket)?;

        // Parse all template params and the closing bracket.
        let mut tmpl_params = vec![];
        let end_pos = loop {
            // Parse the template param (there must be at least one).
            tmpl_params.push(TmplParam::from(tokens)?);

            // The next token should either be a comma or the closing bracket.
            match Module::parse_expecting_any(
                tokens,
                HashSet::from([TokenKind::Comma, TokenKind::RightBracket]),
            )? {
                Token {
                    kind: TokenKind::RightBracket,
                    end,
                    ..
                } => {
                    break end;
                }

                _ => {
                    // Allow trailing commas.
                    if let Some(token) = Module::parse_optional(tokens, TokenKind::RightBracket) {
                        break token.end.clone();
                    }
                }
            };
        };

        Ok(TmplParams {
            params: tmpl_params,
            start_pos,
            end_pos,
        })
    }

    /// Creates a new set of template params with default (zero) start and end position.
    pub fn new_with_default_pos() -> Self {
        TmplParams {
            params: vec![],
            start_pos: Default::default(),
            end_pos: Default::default(),
        }
    }
}
