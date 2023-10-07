use crate::lexer::pos::Locatable;
use crate::lexer::pos::Position;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::error::ParseResult;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::program::Program;
use crate::parser::stream::Stream;
use crate::{locatable_impl, util};

/// Represents a trait declaration.
#[derive(Debug, Clone)]
pub struct Trait {
    pub name: String,
    pub fn_sigs: Vec<FunctionSignature>,
    start_pos: Position,
    end_pos: Position,
}

impl PartialEq for Trait {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && util::vecs_eq(&self.fn_sigs, &other.fn_sigs)
    }
}

locatable_impl!(Trait);

impl Trait {
    /// Parses a trait declaration. Expects token sequences of the form
    ///
    ///     trait <name> {
    ///         <fn_sig>...
    ///     }
    ///
    /// where
    ///  - `name` is an identifier representing the name of the trait
    ///  - `fn_sig` is a function signature in the trait (see `FunctionSignature::from`).
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Parse `trait` and get this trait declaration starting position.
        let start_pos = Program::parse_expecting(tokens, TokenKind::Trait)?.start;

        // Parse the trait name and left brace.
        let name = Program::parse_identifier(tokens)?;
        Program::parse_expecting(tokens, TokenKind::LeftBrace)?;

        // Parse all the function signatures in the trait, followed by the closing brace.
        let mut fn_sigs = vec![];
        let end_pos = loop {
            if let Some(token) = Program::parse_optional(tokens, TokenKind::RightBrace) {
                break token.end;
            }

            fn_sigs.push(FunctionSignature::from(tokens)?);
        };

        Ok(Trait {
            name,
            fn_sigs,
            start_pos,
            end_pos,
        })
    }
}
