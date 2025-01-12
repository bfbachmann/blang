use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::func_sig::FunctionSignature;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

/// Represents a set of external function declarations.
#[derive(Clone, Debug, Eq)]
pub struct ExternFn {
    pub fn_sig: FunctionSignature,
    pub maybe_link_name: Option<String>,
    pub is_pub: bool,
    pub span: Span,
}

impl Hash for ExternFn {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.fn_sig.hash(state);
    }
}

impl PartialEq for ExternFn {
    fn eq(&self, other: &Self) -> bool {
        self.fn_sig == other.fn_sig
    }
}

impl Display for ExternFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "extern {}", self.fn_sig)
    }
}

locatable_impl!(ExternFn);

impl ExternFn {
    /// Attempts to parse an external function declaration from the token sequence.
    /// Expects token sequences of one of the following forms:
    ///
    ///     pub extern <fn_sig>
    ///     pub extern "name" <fn_sig>
    ///
    /// where
    ///  - `fn_sig` is a function signature (see `FunctionSignature::from`)
    ///  - `name` is the optional name to link against in codegen
    ///  - `pub` is optional.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let is_pub = Module::parse_optional(tokens, TokenKind::Pub).is_some();
        let start_pos = Module::current_position(tokens);

        // Parse the `extern` token.
        Module::parse_expecting(tokens, TokenKind::Extern)?;

        // Parse the optional extern name.
        let maybe_link_name = match tokens.peek_next() {
            Some(Token {
                kind: TokenKind::StrLiteral(name),
                ..
            }) => {
                let result = Some(name.clone());
                tokens.next();
                result
            }
            _ => None,
        };

        // Parse the function signature.
        let fn_sig = FunctionSignature::from(tokens)?;
        let end_pos = fn_sig.end_pos().clone();

        Ok(ExternFn {
            fn_sig,
            maybe_link_name,
            is_pub,
            span: Span { start_pos, end_pos },
        })
    }
}
