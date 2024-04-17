use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::func_sig::FunctionSignature;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

/// Represents a set of external function declarations.
#[derive(Clone, Debug, Eq)]
pub struct Extern {
    pub fn_sig: FunctionSignature,
    start_pos: Position,
    end_pos: Position,
}

impl Hash for Extern {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.fn_sig.hash(state);
    }
}

impl PartialEq for Extern {
    fn eq(&self, other: &Self) -> bool {
        self.fn_sig == other.fn_sig
    }
}

impl Display for Extern {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "extern {}", self.fn_sig)
    }
}

locatable_impl!(Extern);

impl Extern {
    /// Attempts to parse an external function declaration from the token sequence.
    /// Expects token sequences of one of the following forms:
    ///
    ///     extern <fn_sig>
    ///
    /// where
    ///  - `fn_sig` is a function signature (see `FunctionSignature::from`).
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let start_pos = Module::current_position(tokens);

        // Parse the `extern` token.
        Module::parse_expecting(tokens, TokenKind::Extern)?;

        // Parse the function signature.
        let fn_sig = FunctionSignature::from(tokens)?;
        let end_pos = fn_sig.end_pos().clone();

        Ok(Extern {
            fn_sig,
            start_pos,
            end_pos,
        })
    }
}
