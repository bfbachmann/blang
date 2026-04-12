use crate::analyzer::ast::arg::AArg;
use crate::analyzer::ast::array::AArrayType;
use crate::analyzer::ast::func::{AFn, AFnSig};
use crate::analyzer::ast::pointer::APointerType;
use crate::analyzer::ast::r#enum::AEnumType;
use crate::analyzer::ast::r#struct::AField;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::type_store::{GetType, TypeKey};
use crate::codegen::func::{DICtx, FnCodeGen};
use crate::lexer::pos::{Position, Span};
use crate::parser::{FileID, SrcInfo};
use inkwell::debug_info::{
    AsDIScope, DIBasicType, DICompositeType, DIDerivedType, DIFile, DIFlagsConstants,
    DILocalVariable, DILocation, DIScope, DISubroutineType, DIType, DWARFEmissionKind,
    DWARFSourceLanguage, DebugInfoBuilder,
};
use inkwell::module::Module;
use inkwell::values::{AsValueRef, BasicValueEnum, PointerValue};
use inkwell::AddressSpace;
use llvm_sys::debuginfo::{
    LLVMDIBuilderInsertDbgValueRecordBefore, LLVMDIBuilderInsertDeclareRecordBefore, LLVMDIFlags,
    LLVMDWARFTypeEncoding,
};
use std::path::PathBuf;

const DW_ATE_BOOLEAN: LLVMDWARFTypeEncoding = 2;
const DW_ATE_FLOAT: LLVMDWARFTypeEncoding = 4;
const DW_ATE_SIGNED: LLVMDWARFTypeEncoding = 5;
const DW_ATE_UNSIGNED: LLVMDWARFTypeEncoding = 7;
const DW_ATE_UNSIGNED_CHAR: LLVMDWARFTypeEncoding = 8;

/// Creates a new debug info builder and compile unit for the file.
pub fn new_di_ctx<'ctx>(
    src_info: &SrcInfo,
    file_id: FileID,
    ll_module: &Module<'ctx>,
) -> DICtx<'ctx> {
    let (dir, file_name) = src_info.dir_and_file_name(file_id);
    let file = PathBuf::from(dir).join(file_name);
    let (di_builder, di_cu) = ll_module.create_debug_info_builder(
        true,
        DWARFSourceLanguage::C,
        file.to_str().unwrap(),
        src_info.cwd.to_str().unwrap(),
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
    fn di_builder(&self) -> Option<&DebugInfoBuilder<'ctx>> {
        self.di_ctx.as_ref().map(|c| &c.di_builder)
    }

    /// Generates and sets debug info about a function on the current function.
    pub(crate) fn set_di_subprogram(&mut self, func: &AFn, mangled_name: &str) {
        if self.di_ctx.is_none() {
            return;
        }

        let di_scope = self.di_ctx.as_ref().unwrap().di_cu.as_debug_info_scope();
        let di_file = self.di_file_from_id(func.span.file_id);
        let di_subroutine_type = self.gen_di_subroutine_type(&func.signature);

        let di_subprog = self.di_builder().unwrap().create_function(
            di_scope,
            &func.signature.name,
            Some(mangled_name),
            di_file,
            func.span.start_pos.line,
            di_subroutine_type,
            true,
            true,
            func.body.span.start_pos.line,
            LLVMDIFlags::PUBLIC,
            false, // TODO: Not sure if this should be true in some cases.
        );

        self.ll_fn.unwrap().set_subprogram(di_subprog);
    }

    pub(crate) fn gen_di_fn_param(&mut self, arg: &AArg, arg_no: u32) {
        if self.di_ctx.is_none() {
            return;
        }

        let di_type = self.gen_di_type(arg.type_key);
        self.di_builder().unwrap().create_parameter_variable(
            self.cur_di_scope(),
            &arg.name,
            arg_no,
            self.di_ctx.as_ref().unwrap().di_cu.get_file(),
            arg.span.start_pos.line,
            di_type,
            true,
            LLVMDIFlags::PUBLIC,
        );

        // TODO: Set arg value.
    }

    /// Generates debug info about a function type.
    fn gen_di_subroutine_type(&mut self, fn_sig: &AFnSig) -> DISubroutineType<'ctx> {
        let di_file = self.di_file_from_id(fn_sig.span.file_id);

        let mut di_param_types = vec![];

        let di_ret_type = match fn_sig.maybe_ret_type_key {
            Some(ret_tk) => {
                let ret_type = self.type_converter.get_type(ret_tk);
                if ret_type.is_composite() {
                    let ptr_type_name = format!("*{}", ret_type.name());
                    let di_type = self.gen_di_type(ret_tk);
                    let di_ptr_type = self.di_builder().unwrap().create_pointer_type(
                        &ptr_type_name,
                        di_type,
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

        self.di_builder().unwrap().create_subroutine_type(
            di_file,
            di_ret_type,
            &di_param_types,
            LLVMDIFlags::PUBLIC,
        )
    }

    /// Generates debug info about an arbitrary type.
    fn gen_di_type(&mut self, type_key: TypeKey) -> DIType<'ctx> {
        if let Some(di_type) = self.di_types.get(&type_key) {
            return *di_type;
        }

        let type_size_bits = self.type_converter.size_of_type(type_key) * 8;

        let di_type = match self.type_converter.get_type(type_key) {
            AType::Bool => self
                .gen_di_basic_type("bool", type_size_bits, Some(DW_ATE_BOOLEAN))
                .as_type(),
            AType::U8 => self
                .gen_di_basic_type("u8", type_size_bits, Some(DW_ATE_UNSIGNED_CHAR))
                .as_type(),
            AType::I8 => self
                .gen_di_basic_type("i8", type_size_bits, Some(DW_ATE_SIGNED))
                .as_type(),
            AType::U16 => self
                .gen_di_basic_type("u16", type_size_bits, Some(DW_ATE_UNSIGNED))
                .as_type(),
            AType::I16 => self
                .gen_di_basic_type("i16", type_size_bits, Some(DW_ATE_SIGNED))
                .as_type(),
            AType::U32 => self
                .gen_di_basic_type("u32", type_size_bits, Some(DW_ATE_UNSIGNED))
                .as_type(),
            AType::I32 => self
                .gen_di_basic_type("i32", type_size_bits, Some(DW_ATE_SIGNED))
                .as_type(),
            AType::F32 => self
                .gen_di_basic_type("f32", type_size_bits, Some(DW_ATE_FLOAT))
                .as_type(),
            AType::I64 => self
                .gen_di_basic_type("i64", type_size_bits, Some(DW_ATE_SIGNED))
                .as_type(),
            AType::U64 => self
                .gen_di_basic_type("u64", type_size_bits, Some(DW_ATE_UNSIGNED))
                .as_type(),
            AType::F64 => self
                .gen_di_basic_type("f64", type_size_bits, Some(DW_ATE_FLOAT))
                .as_type(),
            AType::Int => self
                .gen_di_basic_type("int", type_size_bits, Some(DW_ATE_SIGNED))
                .as_type(),
            AType::Uint => self
                .gen_di_basic_type("uint", type_size_bits, Some(DW_ATE_UNSIGNED))
                .as_type(),
            AType::Str => self.gen_di_str_type(type_key, type_size_bits).as_type(),
            AType::Char => self
                .gen_di_basic_type("char", type_size_bits, Some(DW_ATE_UNSIGNED_CHAR))
                .as_type(),
            AType::Struct(struct_type) => self
                .gen_di_struct_type(
                    type_key,
                    &struct_type.name,
                    &struct_type.fields,
                    struct_type.span,
                )
                .as_type(),
            AType::Enum(enum_type) => self.gen_di_enum_type(type_key, enum_type).as_type(),
            AType::Tuple(tuple_type) => self
                .gen_di_struct_type(
                    type_key,
                    format!("tuple::<{type_key}>").as_str(),
                    &tuple_type.fields,
                    Span::default(), // TODO: Whack span, but not sure what to use instead.
                )
                .as_type(),
            AType::Array(array_type) => self.gen_di_array_type(type_key, array_type).as_type(),
            AType::Pointer(ptr_type) => self.gen_di_ptr_type(type_key, ptr_type).as_type(),
            AType::Function(_) => {
                let di_void_type = self.gen_di_void_type();
                self.di_builder()
                    .unwrap()
                    .create_pointer_type("ptr", di_void_type, 0, 0, AddressSpace::default())
                    .as_type()
            }
            AType::Spec(_) | AType::Generic(_) | AType::Unknown(_) => {
                panic!("unexpected type {type_key}");
            }
        };

        self.di_types.insert(type_key, di_type);
        di_type
    }

    /// Generates debug info for a struct type.
    fn gen_di_struct_type(
        &mut self,
        tk: TypeKey,
        name: &str,
        fields: &[AField],
        span: Span,
    ) -> DICompositeType<'ctx> {
        let di_member_placeholders = fields
            .iter()
            .map(|_| unsafe {
                self.di_builder()
                    .unwrap()
                    .create_placeholder_derived_type(self.ll_ctx)
            })
            .collect::<Vec<_>>();
        let di_member_placeholders_as_ditype = di_member_placeholders
            .iter()
            .map(|ty| ty.as_type())
            .collect::<Vec<_>>();

        let di_file = self.di_ctx.as_ref().unwrap().di_cu.get_file();
        let di_struct_type = self.di_builder().unwrap().create_struct_type(
            self.cur_di_scope(),
            name,
            di_file,
            span.start_pos.line,
            self.type_converter.size_of_type(tk) * 8, // Size in bits
            self.type_converter.align_of_type(tk) * 8, // Align bits
            LLVMDIFlags::PUBLIC,
            None,
            &di_member_placeholders_as_ditype,
            0,
            None,
            format!("{tk}").as_str(),
        );

        let mut offset = 0;
        for (di_placeholder, field) in di_member_placeholders.iter().zip(fields.iter()) {
            let di_field_type = self.gen_di_type(field.type_key);

            // Size and alignment are in bits.
            let field_type_size = self.type_converter.size_of_type(field.type_key) * 8;
            let field_type_align = self.type_converter.align_of_type(field.type_key) * 8;

            let di_member_type = self.di_builder().unwrap().create_member_type(
                di_struct_type.as_debug_info_scope(),
                &field.name,
                di_file,
                field.span.start_pos.line,
                field_type_size,
                field_type_align,
                offset,
                LLVMDIFlags::PUBLIC,
                di_field_type,
            );
            unsafe {
                self.di_builder()
                    .unwrap()
                    .replace_placeholder_derived_type(*di_placeholder, di_member_type);
            }
            offset += field_type_size;
        }

        di_struct_type
    }

    /// Generates debug info for the `str` type.
    fn gen_di_str_type(&mut self, tk: TypeKey, type_size_bits: u64) -> DICompositeType<'ctx> {
        let di_file = self.di_ctx.as_ref().unwrap().di_cu.get_file();

        let ptr_size_bits = self.type_converter.size_of_ptr() as u64 * 8;
        let ptr_align_bits = self.type_converter.align_of_ptr() * 8;
        let di_pointee_type = self
            .gen_di_basic_type("u8", 8, Some(DW_ATE_UNSIGNED_CHAR))
            .as_type();
        let di_ptr_type = self.di_builder().unwrap().create_pointer_type(
            "ptr",
            di_pointee_type,
            ptr_size_bits,
            ptr_align_bits,
            AddressSpace::default(),
        );
        let di_len_type = self
            .gen_di_basic_type("uint", ptr_size_bits, Some(DW_ATE_UNSIGNED))
            .as_type();

        let di_member_types = [di_ptr_type.as_type(), di_len_type];

        let di_member_placeholders = di_member_types
            .iter()
            .map(|_| unsafe {
                self.di_builder()
                    .unwrap()
                    .create_placeholder_derived_type(self.ll_ctx)
            })
            .collect::<Vec<_>>();
        let di_member_placeholders_as_ditype = di_member_placeholders
            .iter()
            .map(|ty| ty.as_type())
            .collect::<Vec<_>>();

        let di_struct_type = self.di_builder().unwrap().create_struct_type(
            self.cur_di_scope(),
            "str",
            di_file,
            0,
            type_size_bits,
            self.type_converter.align_of_type(tk) * 8, // Align bits
            LLVMDIFlags::PUBLIC,
            None,
            &di_member_placeholders_as_ditype,
            0,
            None,
            "str",
        );

        let di_ptr_member_type = self.di_builder().unwrap().create_member_type(
            di_struct_type.as_debug_info_scope(),
            "ptr",
            di_file,
            0,
            ptr_size_bits,
            ptr_align_bits,
            0,
            LLVMDIFlags::PUBLIC,
            di_ptr_type.as_type(),
        );

        let di_len_member_type = self.di_builder().unwrap().create_member_type(
            di_struct_type.as_debug_info_scope(),
            "len",
            di_file,
            0,
            ptr_size_bits,
            ptr_align_bits,
            ptr_size_bits,
            LLVMDIFlags::PUBLIC,
            di_len_type,
        );

        unsafe {
            self.di_builder()
                .unwrap()
                .replace_placeholder_derived_type(di_member_placeholders[0], di_ptr_member_type);
        }
        unsafe {
            self.di_builder()
                .unwrap()
                .replace_placeholder_derived_type(di_member_placeholders[1], di_len_member_type);
        }

        di_struct_type
    }

    /// Generates debug info about an enum type.
    fn gen_di_enum_type(&self, tk: TypeKey, enum_type: &AEnumType) -> DIBasicType<'ctx> {
        // TODO: Implement properly.
        self.di_builder()
            .unwrap()
            .create_basic_type(
                &enum_type.name,
                self.type_converter.size_of_type(tk) * 8, // Size in bits
                LLVMDWARFTypeEncoding::default(),
                LLVMDIFlags::PUBLIC,
            )
            .unwrap()
    }

    /// Generates debug info about an array type.
    fn gen_di_array_type(&mut self, tk: TypeKey, array_type: &AArrayType) -> DICompositeType<'ctx> {
        let elem_type = match array_type.maybe_element_type_key {
            Some(elem_tk) => self.gen_di_type(elem_tk),
            None => self.gen_di_void_type(),
        };
        self.di_builder().unwrap().create_array_type(
            elem_type,
            self.type_converter.size_of_type(tk) * 8, // Size in bits
            self.type_converter.align_of_type(tk) * 8, // Align bits
            #[allow(clippy::single_range_in_vec_init)]
            &[(0i64..array_type.len as i64)],
        )
    }

    /// Generates debug info about a pointer type.
    fn gen_di_ptr_type(&mut self, tk: TypeKey, ptr_type: &APointerType) -> DIDerivedType<'ctx> {
        // Make a dummy type first so we can avoid stack overflows in cases where types
        // refer to themselves. This is only a concern with pointer types.
        let di_pointee_type = self.gen_di_void_type();
        let di_ptr_type = self.di_builder().unwrap().create_pointer_type(
            format!("ptr::<{}>", ptr_type.pointee_type_key).as_str(),
            di_pointee_type,
            0,
            0,
            AddressSpace::default(),
        );
        self.di_types.insert(tk, di_ptr_type.as_type());

        // Now we can generate the actual type without worrying about infinite recursion.
        let di_pointee_type = self.gen_di_type(ptr_type.pointee_type_key);
        self.di_builder().unwrap().create_pointer_type(
            format!("ptr::<{}>", ptr_type.pointee_type_key).as_str(),
            di_pointee_type,
            0,
            0,
            AddressSpace::default(),
        )
    }

    /// Generates debug info for an empty type.
    fn gen_di_void_type(&self) -> DIType<'ctx> {
        self.di_builder()
            .unwrap()
            .create_basic_type(
                "void",
                0,
                LLVMDWARFTypeEncoding::default(),
                LLVMDIFlags::PUBLIC,
            )
            .unwrap()
            .as_type()
    }

    /// Creates debug info for a basic type.
    fn gen_di_basic_type(
        &self,
        type_name: &str,
        type_size_bits: u64,
        encoding: Option<LLVMDWARFTypeEncoding>,
    ) -> DIBasicType<'ctx> {
        self.di_builder()
            .unwrap()
            .create_basic_type(
                type_name,
                type_size_bits,
                encoding.unwrap_or_default(),
                LLVMDIFlags::PUBLIC,
            )
            .unwrap()
    }

    /// Creates debug info about the location of a section of source code.
    fn gen_di_location(&self, pos: &Position) -> DILocation<'ctx> {
        self.di_ctx
            .as_ref()
            .unwrap()
            .di_builder
            .create_debug_location(self.ll_ctx, pos.line, pos.col, self.cur_di_scope(), None)
    }

    /// Returns the current debug info scope.
    fn cur_di_scope(&self) -> DIScope<'ctx> {
        match self.ll_fn.unwrap().get_subprogram() {
            Some(s) => s.as_debug_info_scope(),
            None => self.di_ctx.as_ref().unwrap().di_cu.as_debug_info_scope(),
        }
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

    pub(crate) fn unset_di_location(&self) {
        if self.di_ctx.is_none() {
            return;
        }

        self.ll_builder.unset_current_debug_location();
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
        if self.di_ctx.is_none() {
            return;
        }

        let di_file = self.di_ctx.as_ref().unwrap().di_cu.get_file();
        let di_type = self.gen_di_type(type_key);
        let di_var = self.di_builder().unwrap().create_auto_variable(
            self.cur_di_scope(),
            name,
            di_file,
            pos.line,
            di_type,
            true,
            LLVMDIFlags::PUBLIC,
            self.type_converter.align_of_type(type_key),
        );

        let ll_dummy_expr = self
            .di_ctx
            .as_ref()
            .unwrap()
            .di_builder
            .create_expression(vec![]);
        let ll_di_loc = self.gen_di_location(pos);
        let ll_inst = self
            .ll_builder
            .get_insert_block()
            .unwrap()
            .get_last_instruction()
            .unwrap();

        unsafe {
            LLVMDIBuilderInsertDeclareRecordBefore(
                self.di_ctx.as_ref().unwrap().di_builder.as_mut_ptr(),
                ll_var_ptr.as_value_ref(),
                di_var.as_mut_ptr(),
                ll_dummy_expr.as_mut_ptr(),
                ll_di_loc.as_mut_ptr(),
                ll_inst.as_value_ref(),
            );
        }

        self.gen_di_value(di_var, pos, ll_val);
    }

    /// Generates debug info about a variable value at a given point in the source program.
    fn gen_di_value(
        &mut self,
        di_var: DILocalVariable<'ctx>,
        pos: &Position,
        ll_val: BasicValueEnum<'ctx>,
    ) {
        let di_builder = self.di_builder().unwrap();

        let ll_dummy_expr = di_builder.create_expression(vec![]);
        let ll_inst = self
            .ll_builder
            .get_insert_block()
            .unwrap()
            .get_last_instruction()
            .unwrap();
        let ll_di_loc = self.gen_di_location(pos);
        unsafe {
            LLVMDIBuilderInsertDbgValueRecordBefore(
                di_builder.as_mut_ptr(),
                ll_val.as_value_ref(),
                di_var.as_mut_ptr(),
                ll_dummy_expr.as_mut_ptr(),
                ll_di_loc.as_mut_ptr(),
                ll_inst.as_value_ref(),
            )
        };
    }

    fn di_file_from_id(&self, file_id: FileID) -> DIFile<'ctx> {
        let (dir, file_name) = self.src_info.dir_and_file_name(file_id);
        let file = PathBuf::from(dir).join(file_name);

        self.di_ctx
            .as_ref()
            .unwrap()
            .di_builder
            .create_file(file.to_str().unwrap(), self.src_info.cwd.to_str().unwrap())
    }
}
