use std::collections::HashMap;
use std::fmt::Debug;

use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::targets::TargetTriple;
use inkwell::types::{AnyType, AnyTypeEnum, AsTypeRef, BasicMetadataTypeEnum, FunctionType};
use inkwell::values::{
    BasicValue, BasicValueEnum, FunctionValue, IntMathValue, PointerValue,
};
use llvm_sys::core::LLVMFunctionType;
use llvm_sys::prelude::LLVMTypeRef;
use log::debug;

use crate::analyzer::closure::RichClosure;
use crate::analyzer::expr::{RichExpr, RichExprKind};
use crate::analyzer::func::{RichFn, RichRet};
use crate::analyzer::program::RichProg;
use crate::analyzer::statement::RichStatement;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::op::Operator;
use crate::parser::r#type::Type;

#[derive(Debug)]
enum ErrorKind {
    FnVerificationFailed,
}

#[derive(Debug)]
struct CompileError {
    kind: ErrorKind,
    message: String,
}

impl CompileError {
    fn new(kind: ErrorKind, message: &str) -> Self {
        CompileError {
            kind,
            message: message.to_string(),
        }
    }
}

type CompileResult<T> = Result<T, CompileError>;

struct FnCompiler<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    module: &'a Module<'ctx>,

    vars: HashMap<String, PointerValue<'ctx>>,
    fn_value: Option<FunctionValue<'ctx>>,
}

impl<'a, 'ctx> FnCompiler<'a, 'ctx> {
    fn compile(
        context: &'ctx Context,
        builder: &'a Builder<'ctx>,
        fpm: &'a PassManager<FunctionValue<'ctx>>,
        module: &'a Module<'ctx>,
        func: &RichFn,
    ) -> CompileResult<FunctionValue<'ctx>> {
        let mut fn_compiler = FnCompiler {
            context,
            builder,
            fpm,
            module,
            vars: HashMap::new(),
            fn_value: None,
        };

        fn_compiler.compile_fn(func)
    }

    fn compile_fn(&mut self, func: &RichFn) -> CompileResult<FunctionValue<'ctx>> {
        // Build the function signature and create a new "entry" block at the start of the function
        // body.
        let fn_val = self.compile_fn_sig(&func.signature);
        let entry = self.context.append_basic_block(fn_val, "entry");

        // Start building from the beginning of the entry block.
        self.builder.position_at_end(entry);

        // Track the function value so we can reference it later (when we need to allocate variables
        // in its entry block.
        self.fn_value = Some(fn_val);

        // Define function arguments as variables on the stack so they can be referenced in blocks.
        for (arg_val, arg) in fn_val.get_param_iter().zip(func.signature.args.iter()) {
            let alloc = self.create_entry_alloc(arg.name.as_str(), &arg.typ);
            self.builder.build_store(alloc, arg_val);
            self.vars.insert(arg.name.clone(), alloc);
        }

        // Compile the function body.
        self.compile_closure(&func.body)?;

        // TODO: check return value

        // Verify and optimize the function.
        if fn_val.verify(true) {
            self.fpm.run_on(&fn_val);
            Ok(fn_val)
        } else {
            unsafe {
                fn_val.delete();
            }

            Err(CompileError::new(
                ErrorKind::FnVerificationFailed,
                format!("failed to verify function {}", func.signature.name).as_str(),
            ))
        }
    }

    /// Creates a new stack allocation instruction in the entry block of the current function.
    fn create_entry_alloc(&self, name: &str, typ: &Type) -> PointerValue<'ctx> {
        let builder = self.context.create_builder();
        let entry = self.fn_value.unwrap().get_first_basic_block().unwrap();

        match entry.get_first_instruction() {
            Some(first_instr) => builder.position_before(&first_instr),
            None => builder.position_at_end(entry),
        }

        match typ {
            Type::I64 => builder.build_alloca(self.context.i64_type(), name),
            Type::Bool => builder.build_alloca(self.context.bool_type(), name),
            other => panic!("unsupported type {other}"),
        }
    }

    fn compile_closure(&mut self, closure: &RichClosure) -> CompileResult<()> {
        for statement in &closure.statements {
            self.compile_statement(statement)?;
        }

        Ok(())
    }

    fn compile_fn_sig(&self, sig: &FunctionSignature) -> FunctionValue<'ctx> {
        // Define the function in the module.
        let fn_type = self.create_fn_type(sig);
        let fn_val = self.module.add_function(sig.name.as_str(), fn_type, None);

        // Set arg names.
        for (arg_val, arg) in fn_val.get_param_iter().zip(sig.args.iter()) {
            arg_val.set_name(arg.name.as_str());
        }

        fn_val
    }

    /// Converts a `FunctionSignature` into an LLVM `FunctionType`.
    fn create_fn_type(&self, sig: &FunctionSignature) -> FunctionType<'ctx> {
        // Get return type.
        let ret_type = get_type(self.context, sig.return_type.as_ref());

        // Get arg types.
        let arg_types = sig
            .args
            .iter()
            .map(|a| metadata_type_enum(self.context, &a.typ))
            .collect::<Vec<BasicMetadataTypeEnum>>();

        // Create the function type.
        let mut param_types: Vec<LLVMTypeRef> =
            arg_types.iter().map(|val| val.as_type_ref()).collect();
        unsafe {
            FunctionType::new(LLVMFunctionType(
                ret_type.as_type_ref(),
                param_types.as_mut_ptr(),
                param_types.len() as u32,
                false as i32,
            ))
        }
    }

    /// Compiles a statement and returns true if the statement always results in a return.
    /// Statements that would always result in a return are
    ///  - explicit return statements
    ///  - conditionals where every possible branch results in a return
    ///  - loops that always result in a return
    fn compile_statement(&mut self, statement: &RichStatement) -> CompileResult<bool> {
        match statement {
            RichStatement::VariableDeclaration(decl) => {
                panic!("{} not yet supported", decl);
            }
            RichStatement::VariableAssignment(assign) => {
                panic!("{} not yet supported", assign);
            }
            RichStatement::FunctionDeclaration(func) => {
                let fn_val = self.compile_fn(func)?;
                debug!("compiled function:\n{fn_val}");
            }
            RichStatement::Closure(closure) => {
                panic!("{} not yet supported", closure);
            }
            RichStatement::FunctionCall(call) => {
                panic!("{} not yet supported", call);
            }
            RichStatement::Conditional(cond) => {
                panic!("{} not yet supported", cond);
            }
            RichStatement::Loop(closure) => {
                panic!("{} not yet supported", closure);
            }
            RichStatement::Break => {
                panic!("break not yet supported");
            }
            RichStatement::Return(ret) => {
                self.compile_return(ret);
                return Ok(true);
            }
        }

        Ok(false)
    }

    fn compile_return(&self, ret: &RichRet) {
        match &ret.val {
            Some(expr) => {
                let result = self.compile_expr(expr);
                self.builder.build_return(Some(&result));
            }
            None => {
                self.builder.build_return(None);
            }
        }
    }

    fn compile_expr(&self, expr: &RichExpr) -> BasicValueEnum<'ctx> {
        match &expr.kind {
            RichExprKind::VariableReference(name) => match self.vars.get(name) {
                Some(&var) => self.builder.build_load(var.get_type(), var, name.as_str()),
                None => panic!("variable {name} does not exist in this scope"),
            },
            RichExprKind::BoolLiteral(b) => match b {
                true => self
                    .context
                    .bool_type()
                    .const_all_ones()
                    .as_basic_value_enum(),
                false => self.context.bool_type().const_zero().as_basic_value_enum(),
            },
            RichExprKind::I64Literal(i) => self
                .context
                .i64_type()
                .const_int(i.abs() as u64, *i < 0)
                .as_basic_value_enum(),
            // RichExprKind::StringLiteral(String),
            // RichExprKind::FunctionCall(RichFnCall),
            // RichExprKind::AnonFunction(Box<RichFn>),
            RichExprKind::UnaryOperation(op, expr) => {
                // Only the not operator is supported as a unary operator at the moment.
                if *op != Operator::Not {
                    panic!("unexpected unary operator {op}");
                }

                let expr_val = self.compile_expr(expr);
                let result = self.builder.build_not(expr_val.into_int_value(), "test");
                result.as_basic_value_enum()
            }
            // RichExprKind::BinaryOperation(Box<RichExpr>, Operator, Box<RichExpr>),
            // TODO
            other => {
                panic!("{other} not implemented");
            }
        }
    }
}

struct Compiler<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    module: &'a Module<'ctx>,
    program: &'a RichProg,
}

impl<'a, 'ctx> Compiler<'a, 'ctx> {
    fn compile(program: &RichProg, target_triple: Option<&str>) -> CompileResult<()> {
        let ctx = Context::create();
        let builder = ctx.create_builder();
        let module = ctx.create_module("main");

        // Set target triple, if one was provided.
        if let Some(target) = target_triple {
            module.set_triple(&TargetTriple::create(target));
        }

        // Set up function pass manager.
        let fpm = PassManager::create(&module);
        fpm.add_instruction_combining_pass();
        fpm.add_reassociate_pass();
        fpm.add_gvn_pass();
        fpm.add_cfg_simplification_pass();
        fpm.add_basic_alias_analysis_pass();
        fpm.add_promote_memory_to_register_pass();
        fpm.add_instruction_combining_pass();
        fpm.add_reassociate_pass();
        fpm.initialize();

        let mut compiler = Compiler {
            context: &ctx,
            builder: &builder,
            fpm: &fpm,
            module: &module,
            program,
        };

        compiler.compile_program()
    }

    fn compile_program(&mut self) -> CompileResult<()> {
        for statement in &self.program.statements {
            match statement {
                RichStatement::FunctionDeclaration(func) => {
                    let result = self.compile_fn(func)?;
                    result.print_to_stderr();
                }
                other => {
                    panic!("{other} not implemented");
                }
            }
        }

        Ok(())
    }

    /// Compiles the function to an LLVM `FunctionValue`.
    fn compile_fn(&mut self, func: &RichFn) -> CompileResult<FunctionValue<'ctx>> {
        FnCompiler::compile(self.context, self.builder, self.fpm, self.module, func)
    }
}

fn get_type<'a>(context: &'a Context, typ: Option<&Type>) -> AnyTypeEnum<'a> {
    match typ {
        None => context.void_type().as_any_type_enum(),
        Some(Type::Bool) => context.bool_type().as_any_type_enum(),
        Some(Type::I64) => context.i64_type().as_any_type_enum(),
        // TODO: string and function types
        Some(Type::Function(sig)) => {
            panic!("not implemented: {sig}")
        }
        Some(Type::String) => {
            panic!("not implemented: string")
        }
    }
}

fn metadata_type_enum<'a>(context: &'a Context, typ: &Type) -> BasicMetadataTypeEnum<'a> {
    match typ {
        Type::I64 => BasicMetadataTypeEnum::from(context.i64_type()),
        Type::Bool => BasicMetadataTypeEnum::from(context.bool_type()),
        other => panic!("unsupported type {}", other),
    }
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::analyzer::program::RichProg;
    use crate::compiler::Compiler;
    use crate::lexer::token::Token;
    use crate::parser::program::Program;

    #[test]
    fn thing() {
        let code = r#"
            fn main() {
                return
            }
            
            fn thing(): bool {
                return !false
            }
        "#;
        let mut tokens = Token::tokenize(Cursor::new(code).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let rich_prog = RichProg::from(prog).expect("should not error");
        Compiler::compile(&rich_prog, None).expect("should not error");
    }
}
