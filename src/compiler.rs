use std::collections::HashMap;
use std::fmt::Debug;

use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::targets::TargetTriple;
use inkwell::types::{
    AnyType, AnyTypeEnum, AsTypeRef, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType,
};
use inkwell::values::{
    BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue,
};
use inkwell::IntPredicate;
use llvm_sys::core::LLVMFunctionType;
use llvm_sys::prelude::LLVMTypeRef;

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
        // Retrieve the function and create a new "entry" block at the start of the function
        // body.
        let fn_val = self
            .module
            .get_function(func.signature.name.as_str())
            .unwrap();
        let entry = self.context.append_basic_block(fn_val, "entry");

        // Start building from the beginning of the entry block.
        self.builder.position_at_end(entry);

        // Track the function value so we can reference it later (when we need to allocate variables
        // in its entry block.
        self.fn_value = Some(fn_val);

        // Define function arguments as variables on the stack so they can be referenced in blocks.
        for (arg_val, arg) in fn_val.get_param_iter().zip(func.signature.args.iter()) {
            self.create_var(arg.name.as_str(), &arg.typ, arg_val);
        }

        // Compile the function body. This will return true if the function already ends in an
        // explicit return statement (or a set of unconditional branches that all return).
        let returns = self.compile_closure(&func.body)?;

        // If the function body does not end in an explicit return, we have to insert one.
        if !returns {
            self.builder.build_return(None);
        }

        // Verify and optimize the function.
        if fn_val.verify(false) {
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

    /// Creates and initializes a new variable with the given name, type, and initial value.
    /// Panics if a variable by the same name already exists.
    fn create_var(&mut self, name: &str, typ: &Type, val: BasicValueEnum) {
        let ptr = self.create_entry_alloc(name, typ);
        self.builder.build_store(ptr, val);
        assert!(self.vars.insert(name.to_string(), ptr).is_none());
    }

    /// Assigns the value to the variable with the given name. Panics if no such variable exists.
    fn assign_var(&mut self, name: &str, val: BasicValueEnum) {
        let var = self.vars.get(name).unwrap();
        self.builder.build_store(*var, val);
    }

    /// Gets the value of the variable with the given name. Panics if no such variable exists.
    fn get_var(&self, name: &str) -> BasicValueEnum<'ctx> {
        let var = self.vars.get(name).unwrap();
        let val = self.builder.build_load(var.get_type(), *var, name);
        val
    }

    /// Creates a new stack allocation instruction in the entry block of the current function.
    fn create_entry_alloc(&self, name: &str, typ: &Type) -> PointerValue<'ctx> {
        let builder = self.context.create_builder();
        let entry = self.fn_value.unwrap().get_first_basic_block().unwrap();

        match entry.get_first_instruction() {
            Some(first_instr) => builder.position_before(&first_instr),
            None => builder.position_at_end(entry),
        }

        builder.build_alloca(get_basic_type(self.context, typ), name)
    }

    /// Compiles all statements in the closure. Returns true if the closure returns unconditionally.
    fn compile_closure(&mut self, closure: &RichClosure) -> CompileResult<bool> {
        let mut returns = false;
        for (i, statement) in closure.statements.iter().enumerate() {
            let returned = self.compile_statement(statement)?;
            if i == closure.statements.len() - 1 {
                returns = returned
            }
        }

        Ok(returns)
    }

    /// Compiles a statement and returns true if the statement always results in a return.
    /// Statements that would always result in a return are
    ///  - explicit return statements
    ///  - conditionals where every possible branch results in a return
    ///  - loops that always result in a return
    fn compile_statement(&mut self, statement: &RichStatement) -> CompileResult<bool> {
        match statement {
            RichStatement::VariableDeclaration(decl) => {
                // Get the value of the expression being assigned to the variable.
                let val = self.compile_expr(&decl.val);

                // Create and initialize the variable.
                self.create_var(decl.name.as_str(), &decl.typ, val);
            }
            RichStatement::VariableAssignment(assign) => {
                let val = self.compile_expr(&assign.val);
                self.assign_var(assign.name.as_str(), val);
            }
            RichStatement::FunctionDeclaration(func) => {
                self.compile_fn(func)?;
            }
            RichStatement::Closure(closure) => {
                panic!("{} not yet supported", closure);
            }
            RichStatement::FunctionCall(call) => {
                // Get the function value from the module.
                let func = self.module.get_function(call.fn_name.as_str()).unwrap();

                // Compile call args.
                let arg_types: Vec<BasicMetadataValueEnum> = call
                    .args
                    .iter()
                    .map(|a| self.compile_expr(a).into())
                    .collect();

                // Compile the function call.
                self.builder
                    .build_call(func, arg_types.as_slice(), call.fn_name.as_str());
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

    /// Compiles a return statement.
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

    /// Compiles an arbitrary expression.
    fn compile_expr(&self, expr: &RichExpr) -> BasicValueEnum<'ctx> {
        match &expr.kind {
            RichExprKind::VariableReference(name) => self.get_var(name),

            RichExprKind::BoolLiteral(b) => self
                .context
                .bool_type()
                .const_int(*b as u64, false)
                .as_basic_value_enum(),

            RichExprKind::I64Literal(i) => self
                .context
                .i64_type()
                .const_int(i.abs() as u64, *i < 0)
                .as_basic_value_enum(),

            // RichExprKind::StringLiteral(String),
            RichExprKind::FunctionCall(call) => {
                // Get the function value from the module.
                let func = self.module.get_function(call.fn_name.as_str()).unwrap();

                // Compile call args.
                let arg_types: Vec<BasicMetadataValueEnum> = call
                    .args
                    .iter()
                    .map(|a| self.compile_expr(a).into())
                    .collect();

                // Compile the function call and return the result.
                self.builder
                    .build_call(func, arg_types.as_slice(), call.fn_name.as_str())
                    .try_as_basic_value()
                    .left()
                    .unwrap()
            }

            // TODO
            // RichExprKind::AnonFunction(Box<RichFn>),
            RichExprKind::UnaryOperation(op, expr) => self.compile_unary_op(op, expr),

            RichExprKind::BinaryOperation(left_expr, op, right_expr) => {
                self.compile_bin_op(left_expr, op, right_expr)
            }

            other => {
                panic!("{other} not implemented");
            }
        }
    }

    /// Compiles a unary operation expression.
    fn compile_unary_op(&self, op: &Operator, expr: &RichExpr) -> BasicValueEnum<'ctx> {
        // Only the not operator is supported as a unary operator at the moment.
        if *op != Operator::Not {
            panic!("unsupported unary operator {op}");
        }

        // Compile the operand expression.
        let expr_val = self.compile_expr(expr);

        // If the value is a pointer (i.e. a variable reference), we need to get the bool
        // value it points to.
        let operand = if expr_val.is_pointer_value() {
            self.builder.build_ptr_to_int(
                expr_val.into_pointer_value(),
                self.context.bool_type(),
                "negatedbool",
            )
        } else {
            expr_val.into_int_value()
        };

        // Build the logical not as the result of the int compare != 0.
        let result = self.builder.build_int_compare(
            IntPredicate::NE,
            operand,
            self.context.bool_type().const_int(0, false),
            "test",
        );

        result
            .const_cast(self.context.bool_type(), false)
            .as_basic_value_enum()
    }

    /// Compiles a binary operation expression.
    fn compile_bin_op(
        &self,
        left_expr: &RichExpr,
        op: &Operator,
        right_expr: &RichExpr,
    ) -> BasicValueEnum<'ctx> {
        let lhs = self.compile_expr(left_expr);
        let rhs = self.compile_expr(right_expr);

        match op {
            // Arithmetic operators.
            Operator::Add
            | Operator::Subtract
            | Operator::Multiply
            | Operator::Divide
            | Operator::Modulo => self.compile_arith_op(lhs, op, rhs).as_basic_value_enum(),

            // Comparators.
            Operator::EqualTo
            | Operator::NotEqualTo
            | Operator::GreaterThan
            | Operator::LessThan
            | Operator::GreaterThanOrEqual
            | Operator::LessThanOrEqual => self.compile_cmp(lhs, op, rhs).as_basic_value_enum(),

            // Logical operators.
            Operator::LogicalAnd | Operator::LogicalOr => {
                self.compile_logical_op(lhs, op, rhs).as_basic_value_enum()
            }

            other => panic!("unsupported operator {other}"),
        }
    }

    /// Compiles a logical (boolean) operation expression.
    fn compile_logical_op(
        &self,
        lhs: BasicValueEnum<'ctx>,
        op: &Operator,
        rhs: BasicValueEnum<'ctx>,
    ) -> IntValue<'ctx> {
        // Expect both operands to be of type bool.
        let lhs = self.get_bool(lhs);
        let rhs = self.get_bool(rhs);

        match op {
            Operator::LogicalAnd => self.builder.build_and(lhs, rhs, "and"),
            Operator::LogicalOr => self.builder.build_or(lhs, rhs, "or"),
            other => panic!("unexpected logical operator {other}"),
        }
    }

    /// Compiles a comparison operation expression.
    fn compile_cmp(
        &self,
        lhs: BasicValueEnum<'ctx>,
        op: &Operator,
        rhs: BasicValueEnum<'ctx>,
    ) -> IntValue<'ctx> {
        // TODO: will it work if we always treat operands as ints?
        let lhs = self.get_int(lhs);
        let rhs = self.get_int(rhs);

        match op {
            Operator::EqualTo => self
                .builder
                .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq"),
            Operator::NotEqualTo => {
                self.builder
                    .build_int_compare(IntPredicate::NE, lhs, rhs, "ne")
            }
            Operator::GreaterThan => {
                self.builder
                    .build_int_compare(IntPredicate::SGT, lhs, rhs, "gt")
            }
            Operator::LessThan => self
                .builder
                .build_int_compare(IntPredicate::SLT, lhs, rhs, "lt"),
            Operator::GreaterThanOrEqual => {
                self.builder
                    .build_int_compare(IntPredicate::SGE, lhs, rhs, "ge")
            }
            Operator::LessThanOrEqual => {
                self.builder
                    .build_int_compare(IntPredicate::SLE, lhs, rhs, "le")
            }
            other => panic!("unexpected comparison operator {other}"),
        }
    }

    /// Compiles a binary arithmetic operation expression.
    fn compile_arith_op(
        &self,
        lhs: BasicValueEnum<'ctx>,
        op: &Operator,
        rhs: BasicValueEnum<'ctx>,
    ) -> IntValue<'ctx> {
        // Expect both operands to be of type i64.
        let lhs = self.get_int(lhs);
        let rhs = self.get_int(rhs);

        match op {
            Operator::Add => self.builder.build_int_add(lhs, rhs, "sum"),
            Operator::Subtract => self.builder.build_int_sub(lhs, rhs, "diff"),
            Operator::Multiply => self.builder.build_int_mul(lhs, rhs, "prod"),
            Operator::Divide => self.builder.build_int_signed_div(lhs, rhs, "quot"),
            Operator::Modulo => self.builder.build_int_signed_rem(lhs, rhs, "rem"),
            other => panic!("unexpected arithmetic operator {other}"),
        }
    }

    /// Returns the given value as a boolean int value. This is useful for cases where the value may
    /// by a pointer to a bool.
    fn get_bool(&self, val: BasicValueEnum<'ctx>) -> IntValue<'ctx> {
        if val.is_pointer_value() {
            self.builder.build_ptr_to_int(
                val.into_pointer_value(),
                self.context.bool_type(),
                "ptrtobool",
            )
        } else {
            val.into_int_value()
        }
    }

    /// Returns the given value as an int value. This is useful for cases where the value may by
    /// a pointer to an int.
    fn get_int(&self, val: BasicValueEnum<'ctx>) -> IntValue<'ctx> {
        if val.is_pointer_value() {
            self.builder.build_ptr_to_int(
                val.into_pointer_value(),
                self.context.i64_type(),
                "ptrtoint",
            )
        } else {
            val.into_int_value()
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
    /// Compiles the program for the given target. If there is no target, compiles the program for
    /// the host system.
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

        compiler.compile_program()?;
        compiler.module.print_to_stderr();

        Ok(())
    }

    /// Compiles the program.
    fn compile_program(&mut self) -> CompileResult<()> {
        // Do one shallow pass to define all top-level functions in the module.
        for statement in &self.program.statements {
            match statement {
                RichStatement::FunctionDeclaration(func) => {
                    self.compile_fn_sig(&func.signature);
                }
                _ => {}
            }
        }

        for statement in &self.program.statements {
            match statement {
                RichStatement::FunctionDeclaration(func) => {
                    FnCompiler::compile(self.context, self.builder, self.fpm, self.module, func)?;
                }
                other => {
                    panic!("top-level statement {other} not implemented");
                }
            }
        }

        if let Err(e) = self.module.verify() {
            panic!("module verification failed: {}", e);
        }

        Ok(())
    }

    /// Defines the given function in the current module based on the function signature.
    fn compile_fn_sig(&self, sig: &FunctionSignature) {
        // Define the function in the module.
        let fn_type = self.create_fn_type(sig);
        let fn_val = self.module.add_function(sig.name.as_str(), fn_type, None);

        // Set arg names.
        for (arg_val, arg) in fn_val.get_param_iter().zip(sig.args.iter()) {
            arg_val.set_name(arg.name.as_str());
        }
    }

    /// Converts a `FunctionSignature` into an LLVM `FunctionType`.
    fn create_fn_type(&self, sig: &FunctionSignature) -> FunctionType<'ctx> {
        // Get return type.
        let ret_type = get_any_type(self.context, sig.return_type.as_ref());

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
}

fn get_basic_type<'a>(context: &'a Context, typ: &Type) -> BasicTypeEnum<'a> {
    match typ {
        Type::Bool => context.bool_type().as_basic_type_enum(),
        Type::I64 => context.i64_type().as_basic_type_enum(),
        other => {
            panic!("invalid basic type {other}");
        }
    }
}

fn get_any_type<'a>(context: &'a Context, typ: Option<&Type>) -> AnyTypeEnum<'a> {
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
                i64 val = other(2, 10)
            }
            
            fn thing(bool b): bool {
                bool a = true
                return !a || b
            }
            
            fn other(i64 a, i64 b): i64 {
                return a * b + a / 2 - 1
            }
        "#;
        let mut tokens = Token::tokenize(Cursor::new(code).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let rich_prog = RichProg::from(prog).expect("should not error");
        Compiler::compile(&rich_prog, None).expect("should not error");
    }
}
