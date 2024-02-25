use std::hash::{Hash, Hasher};

use crate::lexer::pos::Locatable;
use crate::lexer::pos::Position;
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
    start_pos: Position,
    end_pos: Position,
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
    ///     spec <name> {
    ///         <fn_sig>...
    ///     }
    ///
    /// where
    ///  - `name` is an identifier representing the name of the spec
    ///  - `fn_sig` is a function signature in the spec (see `FunctionSignature::from`).
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Parse `spec` and get this spec declaration starting position.
        let start_pos = Module::parse_expecting(tokens, TokenKind::Spec)?.start;

        // Parse the spec name and left brace.
        let name = Module::parse_identifier(tokens)?;
        Module::parse_expecting(tokens, TokenKind::LeftBrace)?;

        // Parse all the function signatures in the spec, followed by the closing brace.
        let mut fn_sigs = vec![];
        let end_pos = loop {
            if let Some(token) = Module::parse_optional(tokens, TokenKind::RightBrace) {
                break token.end;
            }

            fn_sigs.push(FunctionSignature::from(tokens)?);
        };

        Ok(Spec {
            name,
            fn_sigs,
            start_pos,
            end_pos,
        })
    }
}
