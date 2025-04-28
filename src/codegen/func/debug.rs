use crate::analyzer::ast::arg::AArg;
use crate::analyzer::ast::func::{AFn, AFnSig};
use crate::analyzer::type_store::{GetType, TypeKey};
use crate::codegen::func::{DICtx, FnCodeGen};
use crate::lexer::pos::Position;
use crate::parser::{FileID, SrcInfo};
use inkwell::debug_info::{
    AsDIScope, DIFile, DIFlagsConstants, DILocalVariable, DILocation, DIScope, DISubroutineType,
    DIType, DWARFEmissionKind, DWARFSourceLanguage,
};
use inkwell::module::Module;
use inkwell::values::{BasicValueEnum, PointerValue};
use inkwell::AddressSpace;
use llvm_sys::debuginfo::{LLVMDIFlags, LLVMDWARFTypeEncoding};

/// Creates a new debug info builder and compile unit for the file.
pub fn new_di_ctx<'ctx>(
    src_info: &SrcInfo,
    file_id: FileID,
    ll_module: &Module<'ctx>,
) -> DICtx<'ctx> {
    let (dir, file_name) = src_info.dir_and_file_name(file_id);
    let (di_builder, di_cu) = ll_module.create_debug_info_builder(
        true,
        DWARFSourceLanguage::C,
        file_name,
        dir,
        "blang",
        false,
        "",
        0,
        "",
        DWARFEmissionKind::Full,
        0,
        true,
        true,
        "",
        "",
    );

    DICtx { di_builder, di_cu }
}

impl<'a, 'ctx> FnCodeGen<'a, 'ctx> {
    /// Generates and sets debug info about a function on the current function.
    pub(crate) fn set_di_subprogram(&self, func: &AFn, mangled_name: &str) {
        let di_ctx = match &self.di_ctx {
            Some(di_ctx) => di_ctx,
            None => return,
        };

        let di_scope = di_ctx.di_cu.as_debug_info_scope();
        let di_file = self.di_file_from_id(func.span.file_id);
        let di_subroutine_type = self.gen_di_subroutine_type(&func.signature);

        let di_subprog = di_ctx.di_builder.create_function(
            di_scope,
            &func.signature.name,
            Some(&mangled_name),
            di_file,
            func.span.start_pos.line as u32,
            di_subroutine_type,
            true,
            true,
            func.body.span.start_pos.line as u32,
            LLVMDIFlags::PUBLIC,
            false, // TODO: Not sure if this should be true in some cases.
        );

        self.ll_fn.unwrap().set_subprogram(di_subprog);
    }

    pub(crate) fn gen_di_fn_param(&mut self, arg: &AArg, arg_no: u32) {
        let di_ctx = match &self.di_ctx {
            Some(di_ctx) => di_ctx,
            None => return,
        };

        di_ctx.di_builder.create_parameter_variable(
            self.cur_di_scope(),
            &arg.name,
            arg_no,
            di_ctx.di_cu.get_file(),
            arg.span.start_pos.line as u32,
            self.gen_di_type(arg.type_key),
            true,
            LLVMDIFlags::PUBLIC,
        );

        // TODO: Set arg value.
    }

    /// Generates debug info about a function type.
    fn gen_di_subroutine_type(&self, fn_sig: &AFnSig) -> DISubroutineType<'ctx> {
        let di_ctx = self.di_ctx.as_ref().unwrap();
        let di_file = self.di_file_from_id(fn_sig.span.file_id);

        let mut di_param_types = vec![];

        let di_ret_type = match fn_sig.maybe_ret_type_key {
            Some(ret_tk) => {
                let ret_type = self.type_converter.get_type(ret_tk);
                if ret_type.is_composite() {
                    let ptr_type_name = format!("*{}", ret_type.name());
                    let di_ptr_type = di_ctx.di_builder.create_pointer_type(
                        &ptr_type_name,
                        self.gen_di_type(ret_tk),
                        64,
                        8,
                        AddressSpace::default(),
                    );
                    di_param_types.push(di_ptr_type);
                    None
                } else {
                    Some(self.gen_di_type(ret_tk))
                }
            }
            None => None,
        };

        let di_param_types: Vec<DIType> = fn_sig
            .args
            .iter()
            .map(|arg| self.gen_di_type(arg.type_key))
            .collect();

        di_ctx.di_builder.create_subroutine_type(
            di_file,
            di_ret_type,
            &di_param_types,
            LLVMDIFlags::PUBLIC,
        )
    }

    /// Generates debug info about a type.
    fn gen_di_type(&self, type_key: TypeKey) -> DIType<'ctx> {
        let di_ctx = self.di_ctx.as_ref().unwrap();

        let typ = self.type_converter.get_type(type_key);
        let type_size = self.type_converter.size_of_type(type_key);

        let mut name = typ.name().to_string();
        if name.is_empty() {
            // TODO: Fix this.
            name = format!("{typ}");
        }

        // TODO: Actually generate proper debug info for the type.
        di_ctx
            .di_builder
            .create_basic_type(
                &name,
                type_size,
                LLVMDWARFTypeEncoding::default(),
                LLVMDIFlags::PUBLIC,
            )
            .unwrap()
            .as_type()
    }

    /// Creates debug info about the location of a section of source code.
    fn gen_di_location(&self, pos: &Position) -> DILocation<'ctx> {
        self.di_ctx
            .as_ref()
            .unwrap()
            .di_builder
            .create_debug_location(
                self.ctx,
                pos.line as u32,
                pos.col as u32,
                self.cur_di_scope(),
                None,
            )
    }

    /// Returns the current debug info scope.
    fn cur_di_scope(&self) -> DIScope<'ctx> {
        self.ll_fn
            .unwrap()
            .get_subprogram()
            .unwrap()
            .as_debug_info_scope()
    }

    /// Attaches the given location as a debug location to the current IR builder so it emits
    /// that debug location with all the IR SSA statements it generates until the next time this
    /// is called.
    pub(crate) fn set_di_location(&self, pos: &Position) {
        if self.di_ctx.is_none() {
            return;
        }

        let di_location = self.gen_di_location(pos);
        self.ll_builder.set_current_debug_location(di_location);
    }

    /// Generates debug info about a variable declaration.
    pub(crate) fn gen_di_declare(
        &mut self,
        name: &str,
        pos: &Position,
        type_key: TypeKey,
        ll_var_ptr: PointerValue,
        ll_val: BasicValueEnum<'ctx>,
    ) {
        let di_ctx = match &self.di_ctx {
            Some(di_ctx) => di_ctx,
            None => return,
        };

        let di_var = di_ctx.di_builder.create_auto_variable(
            self.cur_di_scope(),
            name,
            di_ctx.di_cu.get_file(),
            pos.line as u32,
            self.gen_di_type(type_key),
            true,
            LLVMDIFlags::PUBLIC,
            self.type_converter.align_of_type(type_key),
        );

        di_ctx.di_builder.insert_declare_before_instruction(
            ll_var_ptr,
            Some(di_var),
            None,
            self.gen_di_location(&pos),
            self.ll_builder
                .get_insert_block()
                .unwrap()
                .get_last_instruction()
                .unwrap(),
        );

        self.gen_di_value(di_var, pos, ll_val);
    }

    /// Generates debug info about a variable value at a given point in the source program.
    fn gen_di_value(
        &mut self,
        di_var: DILocalVariable<'ctx>,
        pos: &Position,
        ll_val: BasicValueEnum<'ctx>,
    ) {
        let di_builder = &self.di_ctx.as_ref().unwrap().di_builder;
        di_builder.insert_dbg_value_before(
            ll_val,
            di_var,
            None,
            self.gen_di_location(pos),
            self.ll_builder
                .get_insert_block()
                .unwrap()
                .get_last_instruction()
                .unwrap(),
        );
    }

    fn di_file_from_id(&self, file_id: FileID) -> DIFile<'ctx> {
        let (dir, file_name) = self.src_info.dir_and_file_name(file_id);
        self.di_ctx
            .as_ref()
            .unwrap()
            .di_builder
            .create_file(file_name, dir)
    }
}
