use std::collections::HashMap;

/// Returns true if the vectors have the same length and the same elements in the same positions.
pub fn vectors_are_equal<T: PartialEq>(a: &Vec<T>, b: &Vec<T>) -> bool {
    let match_count = a.iter().zip(b.iter()).filter(|&(a, b)| a == b).count();
    match_count == a.len() && match_count == b.len()
}

/// Returns true if the two optional values are equal.
pub fn optionals_are_equal<T: PartialEq>(a: &Option<T>, b: &Option<T>) -> bool {
    match (a, b) {
        (Some(av), Some(bv)) => av == bv,
        (None, None) => true,
        (_, _) => false,
    }
}

/// Returns true if both maps have the exact same set of keys and share equal values for each key.
pub fn hashmaps_are_equal<K, V>(a: &HashMap<K, V>, b: &HashMap<K, V>) -> bool
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
