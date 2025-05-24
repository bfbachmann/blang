use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::Span;
use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

/// Represents a generic type with a set of specs that serve as constraints
/// on what the generic type can do.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AGenericType {
    pub name: String,
    /// Type keys of the specs that this generic type must implement.
    pub spec_type_keys: HashSet<TypeKey>,
    /// The type key for the type on which this generic is defined.
    pub poly_type_key: TypeKey,
    pub span: Span,
}

impl Hash for AGenericType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.poly_type_key.hash(state);
    }
}

impl Display for AGenericType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (i, type_key) in self.spec_type_keys.iter().enumerate() {
            if i == 0 {
                write!(f, "{}: {}", self.name, type_key)?;
            } else {
                write!(f, " + {}", type_key)?;
            }
        }

        Ok(())
    }
}
