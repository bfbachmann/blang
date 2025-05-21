use std::collections::HashMap;

/// Returns true if both maps have the exact same set of keys and share equal values for each key.
pub fn hashmaps_eq<K, V>(a: &HashMap<K, V>, b: &HashMap<K, V>) -> bool
where
    K: Eq + std::hash::Hash,
    V: PartialEq,
{
    if a.len() != b.len() {
        return false;
    }

    for (a_key, a_val) in a {
        match b.get(a_key) {
            Some(b_val) => {
                if a_val != b_val {
                    return false;
                }
            }
            None => return false,
        }
    }

    true
}

/// Used as a type that implements Drop for defer! macros.
pub struct ScopeCall<F: FnMut()> {
    c: F,
}

impl<F: FnMut()> Drop for ScopeCall<F> {
    fn drop(&mut self) {
        (self.c)();
    }
}

/// Defers the execution of the given expression until the end of the current block.
#[macro_export]
macro_rules! defer {
    ($e:expr) => {
        let _scope_call = ScopeCall {
            c: || -> () {
                $e;
            },
        };
    };
}
