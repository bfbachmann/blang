use std::fmt;
use std::fmt::Formatter;
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::branch::Branch;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;
use crate::{locatable_impl, util};

/// Represents a conditional (i.e. branching if/else if/else statements).
#[derive(Debug, Clone, Eq)]
pub struct Conditional {
    pub branches: Vec<Branch>,
    pub span: Span,
}

impl Hash for Conditional {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.branches.hash(state);
    }
}

impl fmt::Display for Conditional {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "if ...",)
    }
}

impl PartialEq for Conditional {
    fn eq(&self, other: &Self) -> bool {
        util::vecs_eq(&self.branches, &other.branches) && self.span == other.span
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
            span: Span { start_pos, end_pos },
        }
    }

    /// Parses conditionals. Expects token sequences of the forms
    ///
    ///     if <if_cond> <body>
    ///     else if <else_if_cond> <body>
    ///     else <body>
    ///
    /// where
    ///  - the `else if` and `else` branches are optional, and the `else if` branch is repeatable
    ///  - `if_cond` is an expression that represents the `if` branch condition
    ///  - `else_if_cond` is an expression that represents the `else if` branch condition
    ///  - `body` is a statement that represents the branch body.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // The first token should be `if`.
        Module::parse_expecting(tokens, TokenKind::If)?;

        // Parse the rest of the branch (the expression and the closure).
        let branch = Branch::from(tokens, true)?;

        // We now have the first `if` branch. Continue by adding other `else if` branches until
        // there are none left.
        let mut branches = vec![branch];
        loop {
            match tokens.peek_next() {
                Some(&Token {
                    kind: TokenKind::Else,
                    ..
                }) => {
                    // Move past the `else` token.
                    tokens.next();

                    match tokens.peek_next() {
                        // `else if` branch
                        Some(Token {
                            kind: TokenKind::If,
                            ..
                        }) => {
                            // Move past the `if` token.
                            tokens.next();
                            let branch = Branch::from(tokens, true)?;
                            branches.push(branch);
                        }

                        // `else` branch.
                        _ => {
                            // Parse the rest of the branch and add it to the list of branches, then break
                            // because we're reached the end of the conditional.
                            let branch = Branch::from(tokens, false)?;
                            branches.push(branch);
                            break;
                        }
                    }
                }

                _ => {
                    // The next token is not `else`, so we assume it's some new statement and break.
                    break;
                }
            }
        }

        Ok(Conditional::new(branches))
    }
}
