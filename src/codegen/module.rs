use crate::analyzer::ast::ext::AExternFn;
use crate::analyzer::mangling::mangle_type;
use crate::analyzer::type_store::GetType;
use crate::codegen::convert::TypeConverter;
use crate::codegen::error::{CodeGenError, CodeGenResult, ErrorKind};
use crate::codegen::func::debug::new_di_ctx;
use crate::codegen::func::{gen_fn_sig, DICtx, FnCodeGen};
use crate::codegen::program::{init_target_machine, CodeGenConfig, OutputFormat};
use crate::mono_collector::MonoProg;
use crate::parser::{ModID, SrcInfo};
use flamer::flame;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::targets::{FileType, TargetMachine};
use inkwell::values::BasicMetadataValueEnum;
use std::collections::HashMap;
use std::fs;
use std::path::Path;

pub struct ModuleCodeGen<'a, 'ctx> {
    mod_id: ModID,
    ll_ctx: &'a Context,
    ll_builder: Builder<'ctx>,
    ll_mod: Module<'ctx>,
    src_info: &'a SrcInfo,
    prog: &'a MonoProg,
    type_converter: TypeConverter<'ctx>,
}

impl<'a: 'ctx, 'ctx> ModuleCodeGen<'a, 'ctx> {
    fn gen_mod(&mut self) -> CodeGenResult<()> {
        // Set debug info metadata.
        if self.prog.config.emit_debug_info {
            let debug_metadata_version = self.ll_ctx.i32_type().const_int(3, false);
            self.ll_mod.add_basic_value_flag(
                "Debug Info Version",
                inkwell::module::FlagBehavior::Warning,
                debug_metadata_version,
            );
        }

        // Define extern functions.
        if let Some(extern_fns) = self.prog.extern_fns.get(&self.mod_id) {
            for extern_fn in extern_fns.values() {
                self.gen_extern_fn(extern_fn)
            }
        }

        // Define and generate functions.
        self.gen_fns()?;

        // If a main function was defined, generate a wrapping main that calls it.
        // This is necessary because the defined main function will not have the name
        // "main", but rather something like "my_project/my_module/main.bl::main`,
        // so the linker won't locate it as the entrypoint. Generating our own
        // wrapping main also gives us the opportunity to initialize things at
        // runtime, like a GC.
        if let Some(main_fn_tk) = &self.prog.maybe_main_fn_tk {
            self.type_converter.set_type_mapping(HashMap::new());
            let main_fn_sig = self.type_converter.get_type(*main_fn_tk).to_fn_sig();
            let main_mod_id = self
                .src_info
                .mod_info
                .get_id_by_file_id(main_fn_sig.span.file_id)
                .unwrap();
            if self.mod_id == main_mod_id {
                let mangled_name = mangle_type(
                    &self.type_converter,
                    main_fn_sig.type_key,
                    self.type_converter.type_mapping(),
                    &self.prog.type_monomorphizations,
                );
                let ll_main_fn = self.ll_mod.get_function(&mangled_name).unwrap();
                let ll_wrapper_fn = self.ll_mod.add_function(
                    "main",
                    self.ll_ctx.void_type().fn_type(&[], false),
                    None,
                );
                let ll_entry_block = self.ll_ctx.append_basic_block(ll_wrapper_fn, "entry");
                self.ll_builder.position_at_end(ll_entry_block);
                self.ll_builder.build_call(ll_main_fn, &[], "main").unwrap();
                self.ll_builder.build_return(None).unwrap();
            }
        }

        Ok(())
    }

    /// Defines and generates all mono items (functions) in the module.
    fn gen_fns(&mut self) -> CodeGenResult<()> {
        let items = match self.prog.mono_items.get(&self.mod_id) {
            Some(i) => i.clone(),
            None => {
                return Ok(());
            }
        };

        // Define functions.
        for item in items.iter().cloned() {
            self.type_converter.set_type_mapping(item.type_mappings);

            let sig = self
                .type_converter
                .get_type(item.type_key)
                .to_fn_sig()
                .clone();

            // Only use external linkage for pub functions.
            let linkage = match self.prog.pub_fns.contains(&item.type_key) {
                true => Some(Linkage::External),
                false => None,
            };

            gen_fn_sig(
                self.ll_ctx,
                &self.ll_mod,
                &self.type_converter,
                &self.prog.type_monomorphizations,
                &sig,
                linkage,
            );
        }

        // Generate functions.
        let mut di_ctxs: HashMap<ModID, DICtx> = HashMap::new();
        for item in items {
            self.type_converter.set_type_mapping(item.type_mappings);

            let fn_sig = self.type_converter.get_type(item.type_key).to_fn_sig();
            let func = self.prog.fns.get(&fn_sig.type_key).unwrap();
            let file_id = func.span.file_id;

            let maybe_di_ctx = if self.prog.config.emit_debug_info {
                if let Some(di_ctx) = di_ctxs.get_mut(&file_id) {
                    Some(di_ctx)
                } else {
                    let di_ctx = new_di_ctx(self.src_info, file_id, &self.ll_mod);
                    di_ctxs.insert(file_id, di_ctx);
                    Some(di_ctxs.get_mut(&file_id).unwrap())
                }
            } else {
                None
            };

            FnCodeGen::generate(
                self.ll_ctx,
                self.src_info,
                &self.ll_builder,
                maybe_di_ctx,
                &self.ll_mod,
                &self.type_converter,
                self.prog,
                func,
            )?;
        }

        for di_ctx in di_ctxs.into_values() {
            di_ctx.di_builder.finalize();
        }

        Ok(())
    }

    /// Generates an extern function. Extern functions are generated as two functions:
    /// 1. A function with a mangled name that calls 2 and returns its result.
    /// 2. A function with the original unmangled name that is defined without body
    ///    that will be linked externally by the linker.
    fn gen_extern_fn(&mut self, ext_fn: &AExternFn) {
        let fn_sig = &ext_fn.fn_sig;
        let link_name = ext_fn.maybe_link_name.as_ref().unwrap_or(&fn_sig.name);

        // Generate the external function definition with C calling conventions.
        let ll_ext_fn_type = self.type_converter.get_c_fn_type(fn_sig);
        let ll_ext_fn =
            self.ll_mod
                .add_function(link_name.as_str(), ll_ext_fn_type, Some(Linkage::External));
        ll_ext_fn.set_call_conventions(llvm_sys::LLVMCallConv::LLVMCCallConv as u32);

        // Generate the internal function that calls the external one. We'll tell
        // LLVM to always inline this function.
        let mangled_name = mangle_type(
            &self.prog.type_store,
            ext_fn.fn_sig.type_key,
            self.type_converter.type_mapping(),
            &self.prog.type_monomorphizations,
        );
        let linkage = match self.prog.pub_fns.contains(&ext_fn.fn_sig.type_key) {
            true => Some(Linkage::External),
            false => None,
        };
        let ll_intern_fn_type = self.type_converter.get_fn_type(fn_sig.type_key);
        let ll_intern_fn = self
            .ll_mod
            .add_function(&mangled_name, ll_intern_fn_type, linkage);
        let is_sret = fn_sig
            .maybe_ret_type_key
            .is_some_and(|ret_tk| self.type_converter.get_type(ret_tk).is_composite());

        let ll_entry_block = self.ll_ctx.append_basic_block(ll_intern_fn, "entry");
        self.ll_builder.position_at_end(ll_entry_block);

        // Assemble arguments, being careful to dereference any arguments that are supposed to be
        // passed by value.
        let mut ll_args_to_pass: Vec<BasicMetadataValueEnum> = vec![];
        let param_offset = match is_sret {
            true => 1,
            false => 0,
        };

        for (i, arg) in fn_sig.args.iter().enumerate() {
            let mut ll_arg = ll_intern_fn
                .get_nth_param((i + param_offset) as u32)
                .unwrap();

            let needs_deref = self.type_converter.get_type(arg.type_key).is_composite();
            if needs_deref {
                let ll_arg_type = self.type_converter.get_basic_type(arg.type_key);
                ll_arg = self
                    .ll_builder
                    .build_load(ll_arg_type, ll_arg.into_pointer_value(), &arg.name)
                    .unwrap();
            }

            ll_args_to_pass.push(ll_arg.into());
        }

        let ll_ret_val = self
            .ll_builder
            .build_call(ll_ext_fn, &ll_args_to_pass, "extern_result")
            .unwrap()
            .try_as_basic_value()
            .left();

        if let Some(ll_ret_val) = ll_ret_val {
            if is_sret {
                let ll_target_ptr = ll_intern_fn.get_nth_param(0).unwrap().into_pointer_value();
                self.ll_builder
                    .build_store(ll_target_ptr, ll_ret_val)
                    .unwrap();
            } else {
                self.ll_builder.build_return(Some(&ll_ret_val)).unwrap();
                return;
            }
        }

        self.ll_builder.build_return(None).unwrap();
    }
}

/// Generates and optimizes code for the given module.
#[flame]
pub(crate) fn gen_module(src_info: &SrcInfo, prog: &MonoProg, mod_id: ModID) -> CodeGenResult<()> {
    let target_machine = init_target_machine(
        prog.config.target_triple.as_ref(),
        prog.config.optimization_level,
        prog.config.reloc_mode,
    )?;
    let ll_ctx = Context::create();
    let ll_builder = ll_ctx.create_builder();
    let ll_mod = ll_ctx.create_module(&src_info.mod_info.get_by_id(mod_id).path);
    let type_converter = TypeConverter::new(
        &ll_ctx,
        &prog.type_store,
        &prog.type_monomorphizations,
        &target_machine,
    );

    // Set the module triple and data layout based on the target machine.
    let target_data = target_machine.get_target_data();
    let data_layout = target_data.get_data_layout();
    ll_mod.set_triple(&target_machine.get_triple());
    ll_mod.set_data_layout(&data_layout);

    // Create the module code generator and generate the module.
    let mut codegen = ModuleCodeGen {
        mod_id,
        ll_ctx: &ll_ctx,
        src_info,
        ll_builder,
        ll_mod,
        prog,
        type_converter,
    };
    codegen.gen_mod()?;

    // Run optimization passes.
    optimize(&codegen.ll_mod, &prog.config, &target_machine)?;

    // Write generated code to a file.
    emit_to_file(&codegen.ll_mod, &prog.config, &target_machine)
}

/// Runs optimization passes on the LLVM module.
#[flame]
fn optimize(
    ll_mod: &Module,
    config: &CodeGenConfig,
    target_machine: &TargetMachine,
) -> CodeGenResult<()> {
    let (opt_pipeline, opts) = config.optimization_pass_config();
    match ll_mod.run_passes(&opt_pipeline, target_machine, opts) {
        Ok(_) => Ok(()),
        Err(err) => Err(CodeGenError::new(
            ErrorKind::OptimizationFailed,
            &err.to_string(),
        )),
    }
}

/// Writes compilation output to a file.
#[flame]
fn emit_to_file(
    ll_mod: &Module,
    config: &CodeGenConfig,
    target_machine: &TargetMachine,
) -> CodeGenResult<()> {
    let cwd = Path::new(".");
    let mod_path = Path::new(ll_mod.get_name().to_str().unwrap());
    let mod_dir = mod_path.parent().unwrap_or(cwd);

    // Create subdir for caching object/other files.
    let dir_path = config.output_path.parent().unwrap_or(cwd);
    let mod_cache_dir = dir_path.join(".cache").join(mod_dir);
    let mod_cache_dir = mod_cache_dir.as_path();

    if let Err(e) = fs::create_dir_all(mod_cache_dir) {
        return Err(CodeGenError::new(
            ErrorKind::WriteOutFailed,
            format!(
                "failed to create directory {}: {}",
                mod_cache_dir.display(),
                e
            )
            .as_str(),
        ));
    }

    let output_file = mod_cache_dir
        .join(mod_path.file_name().unwrap())
        .with_extension(config.output_format.intermediate_file_extension());

    // Write output to file.
    match config.output_format {
        OutputFormat::LLVMIR => match ll_mod.print_to_file(&output_file) {
            Ok(_) => Ok(()),
            Err(e) => Err(CodeGenError::new(
                ErrorKind::WriteOutFailed,
                e.to_string().as_str(),
            )),
        },

        OutputFormat::LLVMBitcode | OutputFormat::Assembly => {
            match ll_mod.write_bitcode_to_path(&output_file) {
                true => Ok(()),
                false => Err(CodeGenError::new(
                    ErrorKind::WriteOutFailed,
                    format!("failed to write bitcode to {}", output_file.display()).as_str(),
                )),
            }
        }

        OutputFormat::Executable | OutputFormat::Object => {
            let file_type = match config.output_format {
                OutputFormat::Assembly => FileType::Assembly,
                _ => FileType::Object,
            };

            match target_machine.write_to_file(ll_mod, file_type, &output_file) {
                Ok(_) => Ok(()),
                Err(msg) => Err(CodeGenError::new(
                    ErrorKind::WriteOutFailed,
                    msg.to_str().unwrap(),
                )),
            }
        }
    }
}
