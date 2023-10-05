use std::fmt;
use std::fmt::Formatter;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::branch::Branch;
use crate::parser::error::ParseResult;
use crate::parser::program::Program;
use crate::parser::stream::Stream;
use crate::{locatable_impl, util};

/// Represents a conditional (i.e. branching if/else if/else statements).
#[derive(Debug, Clone)]
pub struct Conditional {
    pub branches: Vec<Branch>,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl fmt::Display for Conditional {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // TODO
        write!(f, "if ...",)
    }
}

impl PartialEq for Conditional {
    fn eq(&self, other: &Self) -> bool {
        util::vecs_eq(&self.branches, &other.branches)
            && self.start_pos == other.start_pos
            && self.end_pos == other.end_pos
    }
}

locatable_impl!(Conditional);

impl Conditional {
    /// Creates a new conditional.
    pub fn new(branches: Vec<Branch>) -> Self {
        let start_pos = branches
            .first()
            .unwrap()
            .condition
            .as_ref()
            .unwrap()
            .start_pos()
            .clone();
        let end_pos = branches.last().unwrap().body.end_pos().clone();
        Conditional {
            branches,
            start_pos,
            end_pos,
        }
    }

    /// Parses conditionals. Expects token sequences of the form
    ///
    ///     if <if_cond> {
    ///         ...
    ///     } elsif <elsif_cond> {
    ///         ...
    ///     } else {
    ///         ...
    ///     }
    ///
    /// where
    ///  - the `elsif` and `else` branches are optional, and the `elsif` branch is repeatable
    ///  - `if_cond` is an expression that represents the `if` branch condition
    ///  - `elsif_cond` is an expression that represents the `else if` branch condition
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // The first token should be `if`.
        Program::parse_expecting(tokens, TokenKind::If)?;

        // Parse the rest of the branch (the expression and the closure).
        let branch = Branch::from(tokens, true)?;

        // We now have the first `if` branch. Continue by adding other `elsif` branches until
        // there are none left.
        let mut branches = vec![branch];
        loop {
            match tokens.peek_next() {
                Some(&Token {
                    kind: TokenKind::Elsif,
                    ..
                }) => {
                    // Move past the `elsif` token.
                    tokens.next();

                    // Parse the rest of the branch and add it to the list of branches.
                    let branch = Branch::from(tokens, true)?;
                    branches.push(branch);
                }
                Some(&Token {
                    kind: TokenKind::Else,
                    ..
                }) => {
                    // Move past the `else` token.
                    tokens.next();

                    // Parse the rest of the branch and add it to the list of branches, then break
                    // because we're reached the end of the conditional.
                    let branch = Branch::from(tokens, false)?;
                    branches.push(branch);
                    break;
                }
                _ => {
                    // The next token is not `elsif` or `else`, so we assume it's some new
                    // statement and break.
                    break;
                }
            }
        }

        Ok(Conditional::new(branches))
    }
}
