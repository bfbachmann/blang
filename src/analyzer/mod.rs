//! The Blang analyzer checks the AST that comes from the parser for correctness. Checks include
//! but are not limited to:
//!  - Statement validity checks: checking that special statements like `return`, `break`,
//!    `continue`, and others are only used in context where they make sense.
//!  - Type checks: checking that, where a specific type is expected, a value of that same type is
//!    provided.
//!  - Identifier checks: checking that all types and variables used in the program have valid
//!    definitions and are only used in scopes where those types or variables are accessible.
//!  - Call checks: checking that function calls have the right arguments and that they aren't used
//!    in contexts where their return values match what is expected by the caller.
//!  - Mutability checks: checking that immutable variables are never mutated.
//!  - Move checks: checking that, for types that aren't copied implicitly (generally composite
//!    types like structs), the program follows move rules by not moving the same value more than
//!    once.
//!
//! Once the analyzer has checked the entire program, it returns an new version of the AST it was
//! given with additional information about each AST node like types or control flow hints. It
//! also returns a list of warnings and errors that occurred during analysis that may prevent
//! compilation.

pub mod closure;
pub mod cond;
pub mod error;
pub mod expr;
pub mod func;
mod move_check;
pub mod prog_context;
pub mod program;
pub mod statement;
pub mod r#struct;
pub mod tuple;
pub mod r#type;
pub mod var;
pub mod var_assign;
pub mod var_dec;
pub mod warn;
