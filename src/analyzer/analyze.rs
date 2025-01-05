use std::collections::HashMap;
use std::path::PathBuf;

use crate::analyzer::ast::module::AModule;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::warn::AnalyzeWarning;
use crate::codegen::program::CodeGenConfig;
use crate::fmt::hierarchy_to_string;
use crate::lexer::pos::Position;
use crate::parser::module::Module;
use flamer::flame;

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
pub struct ProgramAnalysis {
    pub ctx: ProgramContext,
    pub analyzed_modules: Vec<AnalyzedModule>,
    pub maybe_main_fn_mangled_name: Option<String>,
}

/// Analyzes all the given modules.
#[flame]
pub fn analyze_modules(modules: Vec<Module>, config: CodeGenConfig) -> ProgramAnalysis {
    let root_mod_path = PathBuf::from(&modules.first().unwrap().path);
    let mods: HashMap<PathBuf, Module> =
        HashMap::from_iter(modules.into_iter().map(|m| (PathBuf::from(&m.path), m)));
    let mut analyzed_mods: HashMap<PathBuf, AnalyzedModule> = HashMap::new();
    let mod_paths = mods.keys().map(|k| k.to_str().unwrap()).collect();
    let mut ctx = ProgramContext::new(root_mod_path.to_str().unwrap(), mod_paths, config);

    // Analyze builtins first.
    for path in mods.keys() {
        if path.starts_with("std/builtins") {
            analyze_module(&mut ctx, &mods, &mut analyzed_mods, &vec![], path);
        }
    }

    analyze_module(&mut ctx, &mods, &mut analyzed_mods, &vec![], &root_mod_path);

    // Try to find the name of the main function in the root module.
    let maybe_main_fn_mangled_name = match ctx.get_fn_sig_by_mangled_name(
        None,
        ctx.mangle_name(None, None, None, "main", true).as_str(),
    ) {
        Some(sig) => Some(sig.mangled_name.clone()),
        None => None,
    };

    ProgramAnalysis {
        ctx,
        analyzed_modules: analyzed_mods.into_values().collect(),
        maybe_main_fn_mangled_name,
    }
}

/// Recursively analyzes modules bottom-up by following imports.
pub fn analyze_module(
    ctx: &mut ProgramContext,
    mods: &HashMap<PathBuf, Module>,
    analyzed_mods: &mut HashMap<PathBuf, AnalyzedModule>,
    mod_chain: &Vec<PathBuf>,
    mod_path: &PathBuf,
) {
    // Append the module we're analyzing to the dependency chain.
    let mut new_mod_chain = mod_chain.clone();
    new_mod_chain.push(mod_path.clone());

    let module = match mods.get(mod_path) {
        Some(m) => m,
        None => panic!("could not find module {}", mod_path.display()),
    };

    // Make sure all modules that this module depends on are analyzed first.
    let mut import_cycle_errs = vec![];
    for used_mod in &module.used_mods {
        let used_mod_path = PathBuf::from(&used_mod.path.raw);

        // Record error and skip this import if it is cyclical.
        if new_mod_chain.contains(&used_mod_path) {
            let mut cycle = new_mod_chain.clone();
            cycle.push(used_mod_path);

            let import_cycle = hierarchy_to_string(
                &cycle
                    .iter()
                    .map(|p| p.to_str().unwrap().to_string())
                    .collect(),
            );
            import_cycle_errs.push(
                AnalyzeError::new(ErrorKind::ImportCycle, "import cycle", used_mod).with_detail(
                    format!("The offending import cycle is: {}", import_cycle).as_str(),
                ),
            );

            continue;
        }

        // Analyze the module only if we have not already done so.
        if !analyzed_mods.contains_key(&used_mod_path) {
            analyze_module(ctx, mods, analyzed_mods, &new_mod_chain, &used_mod_path);
        }
    }

    let analyzed_module = AModule::from(ctx, module);

    // Append the import cycle errors to the module analysis errors.
    let mut errs = std::mem::take(&mut ctx.errors);
    for cycle_err in import_cycle_errs {
        errs.insert(cycle_err.span.start_pos, cycle_err);
    }

    analyzed_mods.insert(
        mod_path.into(),
        AnalyzedModule::new(analyzed_module, errs, std::mem::take(&mut ctx.warnings)),
    );
}
