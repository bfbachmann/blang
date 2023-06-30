use std::collections::VecDeque;

use crate::lexer::token::Token;
use crate::parser::expr::Expression;
use crate::parser::r#type::Type;
use crate::parser::var_assign::VariableAssignment;
use crate::parser::ParseResult;

/// Represents a variable declaration. Each variable declaration must have a valid type, a name,
/// and some value as the result of an expression.
#[derive(Debug, PartialEq)]
pub struct VariableDeclaration {
    typ: Type,
    name: String,
    value: Expression,
}

impl VariableDeclaration {
    pub fn new(typ: Type, name: String, value: Expression) -> Self {
        VariableDeclaration { typ, name, value }
    }

    /// Parses variable declarations. Expects token sequences of the form
    ///
    ///     <type> <name> = <expr>
    ///
    /// where
    ///  - `type` is the variable type
    ///  - `name` is the variable name
    ///  - `expr` is an expression representing the value assigned to the variable
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token(s) should be the variable type.
        let var_type = Type::from(tokens)?;

        // The next tokens should take the form of a variable assignment.
        let assign = VariableAssignment::from(tokens)?;

        Ok(VariableDeclaration::new(
            var_type,
            assign.name,
            assign.value,
        ))
    }
}
