use std::collections::HashSet;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::program::Program;
use crate::parser::r#type::Type;
use crate::parser::stream::Stream;

/// Represents a template parameter. A template parameter has a name and has either one associated
/// type, a set of associated specs, or no associated type or specs (i.e. is a wildcard parameter).
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TmplParam {
    /// The name given to the template parameter.
    pub name: String,
    /// The specs that this template parameter requires.
    pub required_specs: Vec<Type>,
    /// The type that this template parameter requires.
    pub required_type: Option<Type>,
    start_pos: Position,
    end_pos: Position,
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
            name: Program::parse_identifier(tokens)?,
            required_specs: vec![],
            required_type: None,
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
                tmpl_param.required_type = Some(Type::from(tokens)?);
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
                    if Program::parse_optional(tokens, TokenKind::Add).is_none() {
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
}

locatable_impl!(TmplParam);

/// Represents template parameters. A set of template parameters is just a set of generic types,
/// each with an optional set of specs that the type implements, or a single concrete type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TmplParams {
    pub tmpl_params: Vec<TmplParam>,
    start_pos: Position,
    end_pos: Position,
}

locatable_impl!(TmplParams);

impl TmplParams {
    /// Parses a set of template parameters. Expects token sequences of the forms
    ///
    ///     [<type_param>,...]
    ///
    /// where
    ///  - `tmpl_param` is a template parameter (see `TmplParam::from`).
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let start_pos = Program::parse_expecting(tokens, TokenKind::LeftBracket)?.start;

        // Parse all template params and the closing bracket.
        let mut tmpl_params = vec![];
        let end_pos = loop {
            // Parse the template param (there must be at least one).
            tmpl_params.push(TmplParam::from(tokens)?);

            // The next token should either be a comma or the closing bracket.
            match Program::parse_expecting_any(
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
                    if let Some(token) = Program::parse_optional(tokens, TokenKind::RightBracket) {
                        break token.end.clone();
                    }
                }
            };
        };

        Ok(TmplParams {
            tmpl_params,
            start_pos,
            end_pos,
        })
    }
}
