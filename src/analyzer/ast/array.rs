use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{err_invalid_array_size_type, err_mismatched_types};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::Span;
use crate::parser::ast::array::{ArrayInit, ArrayType};
use crate::Locatable;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

/// An array type declaration.
#[derive(Clone, Eq, Debug)]
pub struct AArrayType {
    pub maybe_element_type_key: Option<TypeKey>,
    pub len: u64,
}

impl Hash for AArrayType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.maybe_element_type_key.hash(state);
        self.len.hash(state);
    }
}

impl PartialEq for AArrayType {
    fn eq(&self, other: &Self) -> bool {
        // Empty array types are always equivalent.
        let both_empty = self.len == 0 && other.len == 0;
        both_empty
            || (self.maybe_element_type_key == other.maybe_element_type_key
                && self.len == other.len)
    }
}

impl Display for AArrayType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.maybe_element_type_key {
            Some(key) => {
                write!(f, "[{}; {}]", key, self.len)
            }
            None => write!(f, "[]"),
        }
    }
}

impl AArrayType {
    /// Performs semantic analysis on the given array type.
    pub fn from(ctx: &mut ProgramContext, array_type: &ArrayType) -> AArrayType {
        // Analyze the contained type.
        let mut maybe_element_type_key = array_type
            .maybe_element_type
            .as_ref()
            .map(|element_type| ctx.resolve_type(element_type));

        // Analyze the array type length expression.
        let len_expr = AExpr::from(
            ctx,
            array_type.length_expr.clone(),
            Some(ctx.uint_type_key()),
            false,
            false,
        );

        // Try to evaluate the length expression as a constant `uint`. We'll skip this step if the
        // expression is already of the wrong type.
        let len = if len_expr.type_key != ctx.uint_type_key() {
            0
        } else {
            match len_expr.try_into_const_uint(ctx) {
                Some(u) => {
                    // If the array is empty, we'll also make sure it has no assigned type key
                    // for consistency.
                    if u == 0 {
                        maybe_element_type_key = None;
                    }
                    u
                }
                None => {
                    ctx.insert_err(err_invalid_array_size_type(*array_type.length_expr.span()));
                    0
                }
            }
        };

        AArrayType {
            maybe_element_type_key,
            len,
        }
    }

    /// Returns true if this array type is the same as `other`. Array types are considered the same
    /// if they have the same length and have element types that are considered the same.
    pub fn is_same_as(&self, ctx: &ProgramContext, other: &AArrayType) -> bool {
        // Check array lengths match.
        if self.len != other.len {
            return false;
        }

        // They're the same if they both have length 0.
        if self.len == 0 {
            return true;
        }

        ctx.types_match(
            self.maybe_element_type_key.unwrap(),
            other.maybe_element_type_key.unwrap(),
            false,
        )
    }
}

/// Represents array initialization. Arrays can be initialized as empty, with a list of of values,
/// or with a single value and a repeat count that tells the compiler how many times the value
/// should be duplicated in the array.
#[derive(PartialEq, Debug, Clone)]
pub struct AArrayInit {
    pub values: Vec<AExpr>,
    pub maybe_repeat_count: Option<u64>,
    pub maybe_element_type_key: Option<TypeKey>,
    pub type_key: TypeKey,
    pub span: Span,
}

impl Display for AArrayInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;

        match &self.maybe_repeat_count {
            Some(count) => {
                write!(f, "{}; {}]", self.values.first().unwrap(), count)?;
                return Ok(());
            }

            None => {
                for (i, value) in self.values.iter().enumerate() {
                    match i {
                        0 => write!(f, "{}", value)?,
                        _ => write!(f, ", {}", value)?,
                    };
                }
            }
        }

        write!(f, "]")
    }
}

impl AArrayInit {
    /// Returns a new empty array initialization.
    pub fn new_empty(ctx: &mut ProgramContext) -> AArrayInit {
        AArrayInit::from(ctx, &ArrayInit::new_empty(), None)
    }

    /// Performs semantic analysis on array initialization and returns the analyzed result.
    pub fn from(
        ctx: &mut ProgramContext,
        array_init: &ArrayInit,
        maybe_expected_element_type_key: Option<TypeKey>,
    ) -> AArrayInit {
        // Analyze all the values in the array.
        let mut contained_values = vec![];
        for value_expr in &array_init.values {
            let expr = AExpr::from(
                ctx,
                value_expr.clone(),
                maybe_expected_element_type_key,
                false,
                false,
            );
            contained_values.push(expr);
        }

        // Make sure all the values are of the same type.
        let maybe_element_type_key = if !contained_values.is_empty() {
            let expected_type_key = contained_values.first().unwrap().type_key;

            for value in &contained_values {
                if !ctx.types_match(value.type_key, expected_type_key, false) {
                    let err =
                        err_mismatched_types(ctx, expected_type_key, value.type_key, value.span);
                    ctx.insert_err(err);

                    // Just return an empty array since it's invalid.
                    return AArrayInit {
                        values: vec![],
                        maybe_repeat_count: None,
                        maybe_element_type_key: None,
                        type_key: ctx.unknown_type_key(),
                        span: Default::default(),
                    };
                }
            }

            Some(expected_type_key)
        } else {
            None
        };

        // The repeat count will never be Some if there isn't exactly one element in the array.
        let maybe_repeat_count = match &array_init.maybe_repeat_expr {
            Some(repeat_expr) => {
                let expr = AExpr::from(
                    ctx,
                    repeat_expr.clone(),
                    Some(ctx.uint_type_key()),
                    false,
                    false,
                );
                if expr.type_key != ctx.uint_type_key() {
                    // Default to zero length if the repeat parameter is invalid.
                    Some(0)
                } else {
                    match expr.try_into_const_uint(ctx) {
                        Some(u) => Some(u),
                        None => {
                            ctx.insert_err(err_invalid_array_size_type(*repeat_expr.span()));

                            // Just return an empty array since it's invalid.
                            return AArrayInit {
                                values: vec![],
                                maybe_repeat_count: None,
                                maybe_element_type_key: None,
                                type_key: ctx.unknown_type_key(),
                                span: Default::default(),
                            };
                        }
                    }
                }
            }

            None => None,
        };

        // Insert the new type into the program context now that we've resolved it.
        let type_key = ctx.insert_type(AType::Array(AArrayType {
            len: match &maybe_repeat_count {
                Some(count) => *count,
                None => contained_values.len() as u64,
            },
            maybe_element_type_key,
        }));

        AArrayInit {
            values: contained_values,
            maybe_repeat_count,
            maybe_element_type_key,
            type_key,
            span: array_init.span,
        }
    }

    /// Returns the human-readable version of this array initialization.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let mut s = "[".to_string();

        match &self.maybe_repeat_count {
            Some(count) => s + format!("{}; {}]", self.values.first().unwrap(), count).as_str(),
            None => {
                for (i, val) in self.values.iter().enumerate() {
                    match i {
                        0 => s += val.display(ctx).to_string().as_str(),
                        _ => s += format!(", {}", val.display(ctx)).as_str(),
                    }
                }

                s + "]"
            }
        }
    }
}
