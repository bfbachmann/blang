use std::fmt::{Display, Formatter};

use colored::*;

use crate::lexer::pos::{Locatable, Position};

/// Represents a warning issued by the semantic analyzer.
#[derive(Debug, PartialEq)]
pub struct Warning {
    pub message: String,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Display for Warning {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message.bold())
    }
}

impl Warning {
    /// Creates a new warning message with start and end positions cloned from the locatable.
    pub fn new_from_locatable(message: &str, loc: Box<dyn Locatable>) -> Self {
        Warning {
            message: message.to_string(),
            start_pos: loc.start_pos().clone(),
            end_pos: loc.end_pos().clone(),
        }
    }
}
