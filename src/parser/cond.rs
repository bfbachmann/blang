use std::collections::{HashSet, VecDeque};
use std::fmt;
use std::fmt::Formatter;

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::branch::Branch;
use crate::parser::program::Program;
use crate::parser::ParseResult;
use crate::util;

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
        util::vectors_are_equal(&self.branches, &other.branches)
            && self.start_pos == other.start_pos
            && self.end_pos == other.end_pos
    }
}

impl Locatable for Conditional {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

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

    /// Parses conditionals. Expects token sequences of the forms
    ///
    ///     if <if_cond> {
    ///         ...
    ///     } else if <else_if_cond> {
    ///         ...
    ///     } else {
    ///         ...
    ///     }
    ///
    /// where
    ///  - the `else if` and `else` branches are optional, and the `else if` branch is repeatable
    ///  - `if_cond` is an expression that represents the `if` branch condition
    ///  - `else_if_cond` is an expression that represents the `else if` branch condition
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token should be "if".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::If]))?;

        // Parse the rest of the branch (the expression and the closure).
        let branch = Branch::from(tokens, true)?;

        // We now have the first "if" branch. Continue by adding other "else if" branches until
        // there are none left.
        let mut branches = vec![branch];
        loop {
            match tokens.front() {
                Some(&Token {
                    kind: TokenKind::ElseIf,
                    ..
                }) => {
                    // Pop the "else if" token.
                    tokens.pop_front();

                    // Parse the rest of the branch and add it to the list of branches.
                    let branch = Branch::from(tokens, true)?;
                    branches.push(branch);
                }
                Some(&Token {
                    kind: TokenKind::Else,
                    ..
                }) => {
                    // Pop the "else" token.
                    tokens.pop_front();

                    // Parse the rest of the branch and add it to the list of branches, then break
                    // because we're reached the end of the conditional.
                    let branch = Branch::from(tokens, false)?;
                    branches.push(branch);
                    break;
                }
                _ => {
                    // The next token is not "else if" or "else", so we assume it's some new
                    // statement and break.
                    break;
                }
            }
        }

        Ok(Conditional::new(branches))
    }
}
