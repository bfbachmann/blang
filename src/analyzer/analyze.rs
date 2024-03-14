use crate::analyzer::ast::func::AFnSig;

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use target_lexicon::Triple;

use crate::analyzer::ast::module::AModule;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::move_check::MoveChecker;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeStore;
use crate::analyzer::warn::AnalyzeWarning;
use crate::fmt::hierarchy_to_string;
use crate::lexer::pos::{Locatable, Position};
use crate::parser::ast::arg::Argument;
use crate::parser::ast::func_sig::FunctionSignature;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::r#use::UsedModule;
use crate::parser::ast::statement::Statement;
use crate::parser::module::Module;

/// An analyzed source file along with any errors or warnings that occurred during its analysis.
#[derive(Debug)]
pub struct AnalyzedModule {
    pub module: AModule,
    pub errors: Vec<AnalyzeError>,
    pub warnings: Vec<AnalyzeWarning>,
}

impl AnalyzedModule {
    /// Creates a new analyzed module.
    pub fn new(
        module: AModule,
        errors: HashMap<Position, AnalyzeError>,
        warns: HashMap<Position, AnalyzeWarning>,
    ) -> AnalyzedModule {
        // Extract and sort errors and warnings by their location in the source file.
        let mut errors: Vec<(Position, AnalyzeError)> =
            errors.into_iter().map(|(p, e)| (p, e)).collect();
        errors.sort_by(|(pos1, _), (pos2, _)| pos1.cmp(pos2));

        let mut warnings: Vec<(Position, AnalyzeWarning)> =
            warns.into_iter().map(|(p, e)| (p, e)).collect();
        warnings.sort_by(|(pos1, _), (pos2, _)| pos1.cmp(&pos2));

        AnalyzedModule {
            module,
            errors: errors.into_iter().map(|(_, e)| e).collect(),
            warnings: warnings.into_iter().map(|(_, w)| w.clone()).collect(),
        }
    }
}

/// The result of analysis on a set of source files.
#[derive(Debug)]
pub struct ProgramAnalysis {
    pub type_store: TypeStore,
    pub analyzed_modules: Vec<AnalyzedModule>,
}

/// Analyzes all the given modules.
pub fn analyze_modules(modules: Vec<Module>, target_triple: &Triple) -> ProgramAnalysis {
    let root_mod_path = PathBuf::from(&modules.first().unwrap().path);
    let mods: HashMap<PathBuf, Module> =
        HashMap::from_iter(modules.into_iter().map(|m| (PathBuf::from(&m.path), m)));
    let mut analyzed_mods: HashMap<PathBuf, AnalyzedModule> = HashMap::new();
    let mut ctx = match target_triple.pointer_width() {
        Ok(width) => ProgramContext::new(width.bits()),
        Err(_) => ProgramContext::new_with_host_ptr_width(),
    };

    define_intrinsics(&mut ctx);

    analyze_module::<UsedModule>(
        &mut ctx,
        &mods,
        &mut analyzed_mods,
        &vec![],
        &root_mod_path,
        None,
    );

    ProgramAnalysis {
        type_store: ctx.type_store,
        analyzed_modules: analyzed_mods.into_values().collect(),
    }
}

/// Recursively analyzes modules bottom-up by following imports.
pub fn analyze_module<T: Locatable>(
    ctx: &mut ProgramContext,
    mods: &HashMap<PathBuf, Module>,
    analyzed_mods: &mut HashMap<PathBuf, AnalyzedModule>,
    mod_chain: &Vec<PathBuf>,
    mod_path: &PathBuf,
    maybe_use_loc: Option<&T>,
) {
    // Make sure this module isn't already under analysis. If it is, it means
    // there is a cyclical import.
    let is_import_cycle = mod_chain.contains(&mod_path);

    // Append the module we're analyzing to the dependency chain.
    let mut mod_chain = mod_chain.clone();
    mod_chain.push(mod_path.clone());

    if is_import_cycle {
        ctx.insert_err(
            AnalyzeError::new(
                ErrorKind::ImportCycle,
                "import cycle",
                maybe_use_loc.unwrap(),
            )
            .with_detail(
                format!(
                    "The offending import cycle is: {}",
                    hierarchy_to_string(
                        &mod_chain
                            .iter()
                            .map(|p| p.to_str().unwrap().to_string())
                            .collect()
                    )
                )
                .as_str(),
            ),
        );

        return;
    }

    // Make sure all modules that this module depends on are analyzed first.
    let module = mods.get(mod_path).unwrap();
    let mod_dir = Path::new(mod_path).parent().unwrap_or(Path::new("."));
    for statement in &module.statements {
        if let Statement::Use(used_mod) = statement {
            // Analyze the module only if we have not already done so.
            let used_mod_path = mod_dir.join(used_mod.path.raw.as_str());
            if !analyzed_mods.contains_key(&used_mod_path) {
                analyze_module(
                    ctx,
                    mods,
                    analyzed_mods,
                    &mod_chain,
                    &used_mod_path,
                    Some(used_mod),
                );
            }
        }
    }

    let analyzed_module = AModule::from(ctx, module);

    // Perform move checks and add any errors to our list of errors only if semantic analysis
    // passed. We only do this if analysis returned zero errors because otherwise the move
    // checker could raise superfluous errors.
    if ctx.errors().is_empty() {
        let errors = MoveChecker::check_module(&analyzed_module, ctx.type_store());
        for err in errors {
            ctx.insert_err(err);
        }
    }

    analyzed_mods.insert(
        mod_path.into(),
        AnalyzedModule::new(
            analyzed_module,
            std::mem::take(&mut ctx.errors),
            std::mem::take(&mut ctx.warnings),
        ),
    );
}

/// Defines all intrinsic (built-in) functions, methods, values, and types.
fn define_intrinsics(ctx: &mut ProgramContext) {
    // Generate the method `len(self: str): uint`.
    let maybe_impl_tk = ctx.get_cur_self_type_key();
    ctx.set_cur_self_type_key(Some(ctx.str_type_key()));
    let fn_sig = AFnSig::from(
        ctx,
        &FunctionSignature::new_with_default_pos(
            "len",
            vec![Argument::new_with_default_pos(
                "self",
                Type::new_unresolved("Self"),
                false,
            )],
            Some(Type::new_unresolved("uint")),
        ),
    );
    ctx.insert_member_fn(ctx.str_type_key(), fn_sig);
    ctx.set_cur_self_type_key(maybe_impl_tk);
}
