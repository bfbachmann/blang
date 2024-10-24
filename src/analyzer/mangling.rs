use regex::{Captures, Regex};

use crate::analyzer::type_store::{TypeKey, TypeStore};
use crate::fmt::vec_to_string;

/// Changes the mangled type name in the given `mangled_name` to the mangled name corresponding
/// to `type_key`.
pub fn remangle_name(type_store: &TypeStore, mangled_name: &str, type_key: TypeKey) -> String {
    // This regex partitions a mangled name into 3 parts:
    //  - mod_path: the module path (e.g. `my/mod/path.bl::`)
    //  - type: the type name and optional parameters (e.g. `MyType[1,2,3]`)
    //  - spec_and_name: the optional implemented spec type, path, and function name.
    let re = Regex::new(r"(?P<mod_path>[^:]*::)(?P<type>[^\.]*)(?P<spec_and_name>.*)").unwrap();
    re.replace(mangled_name, |caps: &Captures| {
        let mod_path = &caps["mod_path"];
        let type_name = mangle_type_name(type_store, type_key);
        let spec_and_name = &caps["spec_and_name"];
        format!("{mod_path}{type_name}{spec_and_name}")
    })
    .into_owned()
}

/// Returns a name mangled to the following form.
///
///     <mod_path>::<type_prefix><spec_prefix><path><name>
///
/// where
///  - `mod_path` is the full path of the module in which the symbol is
///    defined (determined by `maybe_mod_name`)
///  - `type_prefix` has the form `<type>.` if there is an impl type on
///    the function (determined by `maybe_impl_type_key`), or is empty
///  - `spec_prefix` has the form `impl:<spec>.` if the function implements a
///    spec (determined by `maybe_spec_type_key`), or is empty
///  - `path` has the form `<f1>.<f2>...` where each item in the sequence
///    is the name of a function inside which the next function is nested
///    (this only applies if `include_fn_path` is `true`)
///  - `<name>` is the name of the symbol.
///
/// If `include_path` is false, `path` will not be included.
pub fn mangle_name(
    type_store: &TypeStore,
    mod_path: &str,
    maybe_impl_type_key: Option<TypeKey>,
    maybe_spec_type_key: Option<TypeKey>,
    fn_path: &str,
    name: &str,
) -> String {
    let typ = match maybe_impl_type_key {
        Some(impl_tk) => format!("{}.", mangle_type_name(type_store, impl_tk)),
        None => "".to_string(),
    };

    let spec = match maybe_spec_type_key {
        Some(spec_tk) => {
            let spec_name = type_store.must_get(spec_tk).to_spec_type().name.as_str();
            format!("impl:{spec_name}.")
        }
        None => "".to_string(),
    };

    format!("{mod_path}::{typ}{spec}{fn_path}{name}")
}

/// Returns the mangled name of the given type.
pub fn mangle_type_name(type_store: &TypeStore, type_key: TypeKey) -> String {
    let impl_type = type_store.must_get(type_key);
    let params = match impl_type.params() {
        Some(params) => format!(
            "[{}]",
            vec_to_string(
                &params.params.iter().map(|p| p.generic_type_key).collect(),
                ",",
            )
        ),
        None => "".to_string(),
    };
    format!("{}{}", impl_type.name(), params)
}
