use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::str::FromStr;

use crate::parser::closure::Closure;
use crate::parser::expr::Expression;
use cranelift::prelude::*;
use cranelift_codegen::ir::UserFuncName;
use cranelift_codegen::isa::{Builder, OwnedTargetIsa};
use cranelift_codegen::settings::{builder, Flags};
use cranelift_codegen::{ir, verify_function};
use target_lexicon::Triple;

use crate::parser::func::Function;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::op::Operator;
use crate::parser::program::Program;
use crate::parser::r#type::Type;
use crate::parser::statement::Statement;
use crate::parser::var_dec::VariableDeclaration;

enum IRGenErrorKind {
    InitFailure,
    FnVerificationFailed,
}

impl fmt::Display for IRGenErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            IRGenErrorKind::InitFailure => write!(f, "Initialization failure"),
            IRGenErrorKind::FnVerificationFailed => write!(f, "Function verification failed"),
        }
    }
}

pub struct IRGenError {
    kind: IRGenErrorKind,
    message: String,
}

impl fmt::Display for IRGenError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "IR generation error: {}: {}", self.kind, self.message)
    }
}

impl IRGenError {
    fn new(kind: IRGenErrorKind, message: &str) -> Self {
        IRGenError {
            kind,
            message: message.to_string(),
        }
    }
}

type IRGenResult<T> = Result<T, IRGenError>;

/// Represents functions for which IR has been generated.
struct GenFn {
    index: u32,
    sig: FunctionSignature,
}

impl GenFn {
    fn new(index: u32, sig: FunctionSignature) -> Self {
        GenFn { index, sig }
    }
}

pub struct GenScope {
    var_index: usize,
}

impl GenScope {
    fn new() -> Self {
        GenScope { var_index: 0 }
    }
}

pub struct GenContext {
    stack: VecDeque<GenScope>,
}

impl GenContext {
    fn new() -> Self {
        GenContext {
            stack: VecDeque::from(vec![GenScope::new()]),
        }
    }

    fn next_var(&mut self) -> usize {
        let scope = self.stack.back_mut().unwrap();
        scope.var_index += 1;
        scope.var_index - 1
    }

    fn push_scope(&mut self) {
        let scope = GenScope::new();
        self.stack.push_back(scope);
    }

    fn pop_scope(&mut self) {
        self.stack.pop_back();
    }
}

pub struct IRGenerator {
    target_isa: OwnedTargetIsa,
    /// Tracks functions for which IR has been generated.
    gen_fns: HashMap<String, GenFn>,
    /// Represents the index of the next function to be generated.
    fn_index: u32,
    /// Stores IR generator settings.
    flags: Flags,
    /// Stores the IR generator context.
    ctx: GenContext,
}

impl IRGenerator {
    /// Creates a new IR generator configured for the target ISA.
    pub fn new_for_target(target_triple: &str) -> IRGenResult<Self> {
        let target_triple = match Triple::from_str(target_triple) {
            Ok(t) => t,
            Err(e) => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    format!("Failed to initialize target triple: {}", e).as_str(),
                ));
            }
        };

        let isa_builder = match isa::lookup(target_triple.clone()) {
            Ok(b) => b,
            Err(e) => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    format!(
                        "Failed to look up ISA builder for target {}: {}",
                        target_triple, e
                    )
                    .as_str(),
                ));
            }
        };

        IRGenerator::from(isa_builder)
    }

    /// Creates a new IR generator configured for the host system.
    pub fn new() -> IRGenResult<Self> {
        let mut isa_builder = match cranelift_native::builder() {
            Ok(builder) => builder,
            Err(err) => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    format!("Failed to initialize ISA builder {}", err).as_str(),
                ));
            }
        };

        if let Err(e) = cranelift_native::infer_native_flags(&mut isa_builder) {
            return Err(IRGenError::new(
                IRGenErrorKind::InitFailure,
                format!("Failure to infer native flags: {}", e).as_str(),
            ));
        }

        IRGenerator::from(isa_builder)
    }

    /// Creates a new IR generator from the given ISA builder.
    fn from(isa_builder: Builder) -> IRGenResult<Self> {
        let flags = Flags::new(builder());
        let target_isa = match isa_builder.finish(flags.clone()) {
            Ok(i) => i,
            Err(e) => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    format!("Failure to finish building ISA: {}", e).as_str(),
                ))
            }
        };

        Ok(IRGenerator {
            target_isa,
            gen_fns: HashMap::new(),
            fn_index: 0,
            flags,
            ctx: GenContext::new(),
        })
    }

    pub fn gen_prog(&mut self, prog: Program) -> IRGenResult<()> {
        // Generate IR for each statement in the program. We're representing the program as an
        // anonymous function with no args or return for convenience so we can reuse code.
        self.gen_fn(&Function::new(
            FunctionSignature::new("", vec![], None),
            Closure::new(prog.statements, None),
        ))
    }

    pub fn gen_statement(
        &mut self,
        fn_builder: &mut FunctionBuilder,
        statement: &Statement,
    ) -> IRGenResult<()> {
        match statement {
            Statement::FunctionDeclaration(func) => self.gen_fn(func),
            Statement::VariableDeclaration(var_decl) => self.gen_var_decl(fn_builder, var_decl),
            Statement::Return(expr) => self.gen_return(fn_builder, expr.as_ref()),
            _ => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    "unimplemented",
                ))
            }
        }
    }

    fn gen_return(
        &mut self,
        fn_builder: &mut FunctionBuilder,
        expr: Option<&Expression>,
    ) -> IRGenResult<()> {
        if expr.is_none() {
            fn_builder.ins().return_(&[]);
        } else {
            let ret_val = self.gen_expr(fn_builder, expr.unwrap());
            fn_builder.ins().return_(&[ret_val]);
        }

        Ok(())
    }

    fn gen_var_decl(
        &mut self,
        fn_builder: &mut FunctionBuilder,
        var_decl: &VariableDeclaration,
    ) -> IRGenResult<()> {
        // Create a new variable.
        let var = self.new_var();

        // Declare the variable type.
        declare_var(fn_builder, var, &var_decl.typ);

        // Define the variable based on its value.
        self.def_var(fn_builder, var, &var_decl.value);

        Ok(())
    }

    fn gen_unary_op(
        &mut self,
        fn_builder: &mut FunctionBuilder,
        op: &Operator,
        expr: &Expression,
    ) -> Value {
        let val = self.gen_expr(fn_builder, expr);
        match op {
            Operator::Not => {
                // Make sure the boolean value is either all 0s (representing false) or all 1s
                // (representing true).
                let tmp = fn_builder.ins().bmask(ir::types::I8, val);
                // Bitwise not to flip all the bits.
                fn_builder.ins().bnot(tmp)
            }
            _ => panic!("invalid unary operator {}", op),
        }
    }

    fn gen_binary_op(
        &mut self,
        fn_builder: &mut FunctionBuilder,
        left: &Expression,
        op: &Operator,
        right: &Expression,
    ) -> Value {
        let left_val = self.gen_expr(fn_builder, left);
        let right_val = self.gen_expr(fn_builder, right);

        match op {
            Operator::Add => fn_builder.ins().iadd(left_val, right_val),
            Operator::Subtract => fn_builder.ins().isub(left_val, right_val),
            Operator::Multiply => fn_builder.ins().imul(left_val, right_val),
            Operator::Divide => fn_builder.ins().udiv(left_val, right_val),
            Operator::Modulo => fn_builder.ins().urem(left_val, right_val),
            Operator::LogicalAnd => fn_builder.ins().band(left_val, right_val),
            Operator::LogicalOr => fn_builder.ins().bor(left_val, right_val),
            // TODO: handle comparators based on operand types
            // Operator::EqualTo =>
            // Operator::NotEqualTo =>
            Operator::GreaterThan => {
                fn_builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThan, left_val, right_val)
            }
            Operator::LessThan => fn_builder
                .ins()
                .icmp(IntCC::SignedLessThan, left_val, right_val),
            Operator::GreaterThanOrEqual => {
                fn_builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, left_val, right_val)
            }
            Operator::LessThanOrEqual => {
                fn_builder
                    .ins()
                    .icmp(IntCC::SignedLessThanOrEqual, left_val, right_val)
            }
            other => panic!("unsupported binary operator {}", other),
        }
    }

    fn gen_expr(&mut self, fn_builder: &mut FunctionBuilder, expr: &Expression) -> Value {
        match expr {
            Expression::BoolLiteral(b) => gen_bool_literal(fn_builder, *b),
            Expression::I64Literal(i) => gen_i64_literal(fn_builder, *i),
            Expression::BinaryOperation(left, op, right) => {
                self.gen_binary_op(fn_builder, left, op, right)
            }
            Expression::UnaryOperation(op, expr) => self.gen_unary_op(fn_builder, op, expr),
            other => {
                panic!("unimplemented expression {}", other)
            }
        }
    }

    fn gen_fn(&mut self, func: &Function) -> IRGenResult<()> {
        // Generate the function signature.
        let sig = self.gen_fn_sig(&func.signature);

        // Create a new function with the signature.
        let fn_index = self.next_fn_index();
        let mut new_func = ir::Function::with_name_signature(UserFuncName::user(0, fn_index), sig);

        // Create a new function builder that we'll use to build this function.
        let mut fn_builder_ctx = FunctionBuilderContext::new();
        let mut fn_builder = FunctionBuilder::new(&mut new_func, &mut fn_builder_ctx);

        // Create a new scope for the function body.
        self.ctx.push_scope();

        // Generate the function body.
        if let Err(e) = self.gen_fn_body(&mut fn_builder, func) {
            return Err(e);
        }

        // Tell the builder we're done with this function and then verify it.
        println!("fn: {}", new_func);
        // fn_builder.finalize();
        if let Err(e) = verify_function(&new_func, &self.flags) {
            return Err(IRGenError::new(
                IRGenErrorKind::FnVerificationFailed,
                e.to_string().as_str(),
            ));
        }

        // Track the generated function so we can reference it later.
        self.gen_fns.insert(
            func.signature.name.clone(),
            GenFn::new(fn_index, func.signature.clone()),
        );

        // Pop the scope since we're exiting it.
        self.ctx.pop_scope();

        println!("{}", new_func.display());
        Ok(())
    }

    fn gen_fn_sig(&mut self, sig: &FunctionSignature) -> Signature {
        // Define the function signature.
        let mut fn_sig = Signature::new(self.target_isa.default_call_conv());

        // Add the function argument types.
        for arg in &sig.args {
            fn_sig.params.push(gen_abi_param(&arg.typ));
        }

        // Add the return type, if there is one.
        if sig.return_type.is_some() {
            fn_sig
                .returns
                .push(gen_abi_param(sig.return_type.as_ref().unwrap()));
        }

        fn_sig
    }

    fn gen_fn_body(
        &mut self,
        fn_builder: &mut FunctionBuilder,
        func: &Function,
    ) -> IRGenResult<()> {
        // Create the entry block, to start emitting code in.
        let block0 = fn_builder.create_block();

        // Since this is the entry block, add block parameters corresponding to the function's
        // parameters.
        fn_builder.append_block_params_for_function_params(block0);

        // Tell the builder to emit code in this block.
        fn_builder.switch_to_block(block0);

        // And, tell the builder that this block will have no further predecessors. Since it's the
        // entry block, it won't have any predecessors.
        fn_builder.seal_block(block0);

        // Generate IR for statements.
        for statement in &func.body.statements {
            if let Err(e) = self.gen_statement(fn_builder, statement) {
                return Err(e);
            }
        }

        Ok(())
    }

    /// Defines the initial value of the given variable from the given expression using the function
    /// builder.
    fn def_var(&mut self, fn_builder: &mut FunctionBuilder, var: Variable, expr: &Expression) {
        let val = self.gen_expr(fn_builder, expr);
        fn_builder.def_var(var, val);
    }

    fn new_var(&mut self) -> Variable {
        Variable::new(self.ctx.next_var())
    }

    fn next_fn_index(&mut self) -> u32 {
        self.fn_index += 1;
        self.fn_index - 1
    }
}

/// Declares the type of the given variable using the function builder.
fn declare_var(fn_builder: &mut FunctionBuilder, var: Variable, typ: &Type) {
    let typ = gen_type(typ);
    fn_builder.declare_var(var, typ);
}

/// Generates an i64 literal with the given value using the function builder.
fn gen_i64_literal(fn_builder: &mut FunctionBuilder, i: i64) -> Value {
    fn_builder.ins().iconst(gen_type(&Type::I64), i)
}

/// Generates a bool literal (represented as u8 because Cranelift doesn't have bools) with the
/// given value using the function builder.
fn gen_bool_literal(fn_builder: &mut FunctionBuilder, b: bool) -> Value {
    let val = match b {
        true => 1,
        false => 0,
    };
    fn_builder.ins().iconst(gen_type(&Type::Bool), val)
}

/// Creates an ABI parameter with the given type.
fn gen_abi_param(typ: &Type) -> AbiParam {
    AbiParam::new(gen_type(typ))
}

/// Converts the given type into a Cranelift type.
fn gen_type(typ: &Type) -> types::Type {
    match typ {
        // Cranelift doesn't have boolean types, so we use i8.
        Type::Bool => types::I8,
        Type::I64 => types::I64,
        other => panic!("unimplemented type {}", other),
    }
}
