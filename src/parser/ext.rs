use std::collections::HashSet;
use std::fmt::{Display, Formatter};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::error::ParseResult;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::program::Program;
use crate::{locatable_impl, util};

/// Represents a set of external function declarations.
#[derive(Debug)]
pub struct Extern {
    pub fn_sigs: Vec<FunctionSignature>,
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for Extern {
    fn eq(&self, other: &Self) -> bool {
        util::vecs_eq(&self.fn_sigs, &other.fn_sigs)
    }
}

impl Clone for Extern {
    fn clone(&self) -> Self {
        Extern {
            fn_sigs: self.fn_sigs.iter().map(|sig| sig.clone()).collect(),
            start_pos: self.start_pos.clone(),
            end_pos: self.end_pos.clone(),
        }
    }
}

impl Display for Extern {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.fn_sigs.len() == 1 {
            write!(f, "extern {}", self.fn_sigs.first().unwrap())
        } else {
            write!(
                f,
                "extern {{ <{} function signatures> }}",
                self.fn_sigs.len()
            )
        }
    }
}

locatable_impl!(Extern);

impl Extern {
    /// Attempts to parse a set of external function declarations from the token sequence. Expects
    /// token sequences of one of the following forms:
    ///
    ///     extern <fn_sig>
    ///     extern {
    ///         <fn_sig>
    ///         ...
    ///     }
    ///
    /// where
    ///  - `fn_sig` is a function signature (see `FunctionSignature::from`).
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let start_pos = Program::current_position(tokens);

        // Parse the `extern` token.
        Program::parse_expecting(tokens, TokenKind::Extern)?;

        // The next token should either be `{` or `fn`.
        match Program::parse_expecting_any(
            tokens,
            HashSet::from([TokenKind::LeftBrace, TokenKind::Fn]),
        )? {
            Token {
                kind: TokenKind::LeftBrace,
                ..
            } => {
                // We're inside an `extern` block, so we need to parse a series of function signatures
                // until we reach the closing curly brace.
                let mut fn_sigs = vec![];
                let end_pos = loop {
                    fn_sigs.push(FunctionSignature::from(tokens)?);

                    if let Some(token) = Program::parse_optional(tokens, TokenKind::RightBrace) {
                        break token.end.clone();
                    }
                };

                Ok(Extern {
                    fn_sigs,
                    start_pos,
                    end_pos,
                })
            }

            Token {
                kind: TokenKind::Fn,
                ..
            } => {
                // This is just a single `extern` function declaration.
                tokens.rewind(1);
                let fn_sig = FunctionSignature::from(tokens)?;
                let end_pos = fn_sig.end_pos().clone();
                Ok(Extern {
                    fn_sigs: vec![fn_sig],
                    start_pos,
                    end_pos,
                })
            }

            _ => unreachable!(),
        }
    }
}
