use std::hash::{Hash, Hasher};

use crate::lexer::pos::Position;
use crate::lexer::pos::{Locatable, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::func_sig::FunctionSignature;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;
use crate::{locatable_impl, util};

/// Represents a spec declaration.
#[derive(Debug, Eq, Clone)]
pub struct Spec {
    pub name: String,
    pub fn_sigs: Vec<FunctionSignature>,
    pub is_pub: bool,
    span: Span,
}

impl Hash for Spec {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.fn_sigs.hash(state);
    }
}

impl PartialEq for Spec {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && util::vecs_eq(&self.fn_sigs, &other.fn_sigs)
    }
}

locatable_impl!(Spec);

impl Spec {
    /// Parses a spec declaration. Expects token sequences of the form
    ///
    ///     pub spec <name> {
    ///         <fn_sig>...
    ///     }
    ///
    /// where
    ///  - `name` is an identifier representing the name of the spec
    ///  - `fn_sig` is a function signature in the spec (see `FunctionSignature::from`)
    ///  - the `pub` keyword is optional.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let is_pub = Module::parse_optional(tokens, TokenKind::Pub).is_some();

        // Parse `spec` and get this spec declaration starting position.
        let start_pos = Module::parse_expecting(tokens, TokenKind::Spec)?
            .span
            .start_pos;

        // Parse the spec name and left brace.
        let name = Module::parse_identifier(tokens)?;
        Module::parse_expecting(tokens, TokenKind::LeftBrace)?;

        // Parse all the function signatures in the spec, followed by the closing brace.
        let mut fn_sigs = vec![];
        let end_pos = loop {
            if let Some(token) = Module::parse_optional(tokens, TokenKind::RightBrace) {
                break token.span.end_pos;
            }

            fn_sigs.push(FunctionSignature::from(tokens)?);
        };

        Ok(Spec {
            name,
            fn_sigs,
            is_pub,
            span: Span { start_pos, end_pos },
        })
    }
}
