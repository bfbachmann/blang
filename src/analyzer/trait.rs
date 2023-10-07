use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func_sig::RichFnSig;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::TypeId;
use crate::format_code;
use crate::parser::r#trait::Trait;
use crate::parser::r#type::Type;

/// Represents a semantically valid trait declaration.
#[derive(PartialEq, Clone, Debug)]
pub struct RichTrait {
    pub name: String,
    pub fn_sigs: Vec<RichFnSig>,
}

impl RichTrait {
    /// Performs semantic analysis on the given trait.
    pub fn from(ctx: &mut ProgramContext, trait_: &Trait) -> Self {
        // Make sure this trait name is not a duplicate.
        if ctx.get_trait(trait_.name.as_str()).is_some() {
            // Record the error and return a placeholder value.
            ctx.add_err(AnalyzeError::new(
                ErrorKind::TraitAlreadyDefined,
                format_code!("another trait named {} already exists", trait_.name).as_str(),
                trait_,
            ));

            return RichTrait {
                name: trait_.name.clone(),
                fn_sigs: vec![],
            };
        }

        // Set the current trait type ID in the program context so instances of the type `This` in
        // the trait methods can be resolved to this trait type.
        ctx.set_this_type_id(Some(TypeId::from(Type::new_unknown(trait_.name.as_str()))));

        // Analyze all the function signatures in the trait.
        let mut fn_sigs = vec![];
        for fn_sig in &trait_.fn_sigs {
            fn_sigs.push(RichFnSig::from(ctx, fn_sig));
        }

        // Unset the current trait type ID since we're done analyzing the trait.
        ctx.set_this_type_id(None);

        let rich_trait = RichTrait {
            name: trait_.name.clone(),
            fn_sigs,
        };

        // Add the new trait to the program context so we can reference it by name later.
        ctx.add_trait(rich_trait.clone());
        rich_trait
    }
}
