/// Represents an operator.
#[derive(Debug, PartialEq)]
pub enum Operator {
    // Basic operators
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,

    // Comparators
    Equals,
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,
}
