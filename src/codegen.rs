use std::collections::HashMap;
use std::fmt;
use std::str::FromStr;

use cranelift::prelude::*;
use cranelift_codegen::isa::Builder;
use cranelift_codegen::settings::{builder, Flags};
use cranelift_codegen::verify_function;
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule, ObjectProduct};
use log::debug;
use target_lexicon::Triple;

use crate::analyzer::closure::RichClosure;
use crate::analyzer::cond::RichCond;
use crate::analyzer::expr::{RichExpr, RichExprKind};
use crate::analyzer::func::{RichFn, RichFnCall, RichRet};
use crate::analyzer::program::RichProg;
use crate::analyzer::statement::RichStatement;
use crate::analyzer::var_assign::RichVarAssign;
use crate::analyzer::var_dec::RichVarDecl;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::op::Operator;
use crate::parser::r#type::Type;

/// Represents kinds of errors that happen during IR generation.
enum IRGenErrorKind {
    InitFailure,
    FnVerificationFailed,
    FnDeclarationFailed,
}

impl fmt::Display for IRGenErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            IRGenErrorKind::InitFailure => write!(f, "initialization failure"),
            IRGenErrorKind::FnVerificationFailed => write!(f, "function verification failed"),
            IRGenErrorKind::FnDeclarationFailed => write!(f, "function declaration failed"),
        }
    }
}

/// Represents errors that happen during IR generation.
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

/// Represents the result of IR generation.
type IRGenResult<T> = Result<T, IRGenError>;

/// Generates IR for functions.
struct FnGenerator<'a> {
    vars: HashMap<String, Variable>,
    fn_builder: FunctionBuilder<'a>,
    var_counter: usize,
    module: &'a mut ObjectModule,
}

impl FnGenerator<'_> {
    /// Returns a new variable identifier that is unique within the current function.
    fn next_var(&mut self) -> usize {
        self.var_counter += 1;
        self.var_counter - 1
    }

    /// Returns a new variable.
    fn new_var(&mut self) -> Variable {
        Variable::new(self.next_var())
    }

    /// Generates IR for the given function.
    fn generate(mut self, rich_fn: &RichFn) -> IRGenResult<()> {
        debug!("generating IR for function {}", &rich_fn.signature.name);
        self.gen_fn_sig(&rich_fn.signature);
        self.gen_fn_body(rich_fn)?;
        self.fn_builder.finalize();
        Ok(())
    }

    /// Generates IR for a statement in the current function.
    fn gen_statement(&mut self, statement: &RichStatement) -> IRGenResult<()> {
        debug!("generating IR for {}", statement);

        match statement {
            // TODO
            // Statement::FunctionDeclaration(func) => self.gen_fn(func),
            // RichStatement::Break
            // RichStatement::Loop()
            // RichStatement::Closure()
            RichStatement::VariableDeclaration(var_decl) => self.gen_var_decl(var_decl),
            RichStatement::VariableAssignment(var_assign) => self.gen_var_assign(var_assign),
            RichStatement::Return(expr) => self.gen_return(expr),
            RichStatement::Conditional(cond) => self.gen_cond(cond),
            RichStatement::FunctionCall(call) => {
                self.gen_call(call);
                Ok(())
            }
            other => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    format!("unimplemented statement {}", other).as_str(),
                ))
            }
        }
    }

    /// Generates IR for assignment of a value to an existing variable.
    fn gen_var_assign(&mut self, var_assign: &RichVarAssign) -> IRGenResult<()> {
        // Generate IR for the expression being assigned to the variable.
        let val = self.gen_expr(&var_assign.val);

        // Look up the variable to which we are assigning.
        let var = self.vars.remove(var_assign.name.as_str()).unwrap();

        // Set the variable value to the result of the expression.
        self.fn_builder.def_var(var, val);

        // Track the new variable value so we can use it later.
        self.vars.insert(var_assign.name.clone(), var);

        Ok(())
    }

    /// Generates IR for a conditional in the current function.
    fn gen_cond(&mut self, rich_cond: &RichCond) -> IRGenResult<()> {
        // Create an end block that we can jump to once we're done executing the branch body.
        let end_block = self.fn_builder.create_block();

        let mut had_else_case = false;
        for branch in &rich_cond.branches {
            if let Some(branch_cond) = &branch.cond {
                // Generate the condition variable and the two blocks that we'll branch to based
                // on the condition.
                let cond_var = self.gen_expr(branch_cond);
                let then_block = self.fn_builder.create_block();
                let else_block = self.fn_builder.create_block();

                // Create the branch instruction that will jump to one of the two blocks based
                // on the condition.
                self.fn_builder
                    .ins()
                    .brif(cond_var, then_block, &[], else_block, &[]);

                // Seal the blocks since there should be nothing else that branches/jumps to them.
                self.fn_builder.seal_block(then_block);
                self.fn_builder.seal_block(else_block);

                // Fill the then block.
                self.fn_builder.switch_to_block(then_block);
                if let Err(e) = self.gen_closure(&branch.body, end_block) {
                    return Err(e);
                }

                // Continue on the else block.
                self.fn_builder.switch_to_block(else_block);
            } else {
                had_else_case = true;

                // There is no branch condition, meaning this is the else case, so we must jump to
                // the then block.
                let then_block = self.fn_builder.create_block();
                self.fn_builder.ins().jump(then_block, &[]);

                // Seal the then block because nothing else will jump/branch to it.
                self.fn_builder.seal_block(then_block);

                // Continue on the then block.
                self.fn_builder.switch_to_block(then_block);

                // Generate instructions for end closure.
                if let Err(e) = self.gen_closure(&branch.body, end_block) {
                    return Err(e);
                }
            }
        }

        // If there was no else case, we need to make sure we don't leave the else block from
        // the last branch dangling. We do this by simply inserting a jump to the end block.
        if !had_else_case {
            self.fn_builder.ins().jump(end_block, &[]);
        }

        // Seal the end block before returning, because we know nothing else will branch/jump to it.
        self.fn_builder.seal_block(end_block);

        // Continue on the end block.
        self.fn_builder.switch_to_block(end_block);

        Ok(())
    }

    /// Generates IR for a closure in the current function. Note that closures can be inline,
    /// branch bodies, or loop bodies.
    fn gen_closure(&mut self, closure: &RichClosure, end_block: Block) -> IRGenResult<()> {
        let mut returned = false;
        for statement in &closure.statements {
            if let Err(e) = self.gen_statement(statement) {
                return Err(e);
            }

            if let RichStatement::Return(_) = statement {
                returned = true
            }
        }

        // We must either return or jump to another block at the end of the closure.
        if !returned {
            self.fn_builder.ins().jump(end_block, &[]);
        }

        Ok(())
    }

    /// Generates IR for return statements in the function.
    fn gen_return(&mut self, rich_ret: &RichRet) -> IRGenResult<()> {
        if let Some(val) = &rich_ret.val {
            let ret_val = self.gen_expr(val);
            self.fn_builder.ins().return_(&[ret_val]);
        } else {
            self.fn_builder.ins().return_(&[]);
        }

        Ok(())
    }

    /// Generates IR for variable declarations in the function.
    fn gen_var_decl(&mut self, var_decl: &RichVarDecl) -> IRGenResult<()> {
        // Create a new variable.
        let var = self.new_var();

        // Declare the variable type.
        self.declare_var(var, &var_decl.typ);

        // Define the variable with its initial value.
        self.def_var(var, &var_decl.val);

        // Track the variable so we can reference it later.
        self.vars.insert(var_decl.name.clone(), var);

        Ok(())
    }

    /// Generates IR for unary operations in the function.
    fn gen_unary_op(&mut self, op: &Operator, expr: &RichExpr) -> Value {
        let val = self.gen_expr(expr);
        match op {
            Operator::Not => {
                // Bitwise not to flip all the bits.
                let result = self.fn_builder.ins().bnot(val);
                // Bitwise and with 1 to ensure the result is either 0 (false) or all 1 (true).
                self.fn_builder.ins().band_imm(result, 1)
            }
            _ => panic!("invalid unary operator {}", op),
        }
    }

    /// Generates IR for binary operations in the function.
    fn gen_binary_op(&mut self, left: &RichExpr, op: &Operator, right: &RichExpr) -> Value {
        let left_val = self.gen_expr(left);
        let right_val = self.gen_expr(right);

        match op {
            Operator::Add => self.fn_builder.ins().iadd(left_val, right_val),
            Operator::Subtract => self.fn_builder.ins().isub(left_val, right_val),
            Operator::Multiply => self.fn_builder.ins().imul(left_val, right_val),
            Operator::Divide => self.fn_builder.ins().udiv(left_val, right_val),
            Operator::Modulo => self.fn_builder.ins().urem(left_val, right_val),
            Operator::LogicalAnd => self.fn_builder.ins().band(left_val, right_val),
            Operator::LogicalOr => self.fn_builder.ins().bor(left_val, right_val),
            Operator::EqualTo => match (&left.typ, &right.typ) {
                (Type::Bool, Type::Bool) => {
                    // Compare the bools. This will return -1 if they're equal and -0 otherwise.
                    let result = self
                        .fn_builder
                        .ins()
                        .icmp(IntCC::Equal, left_val, right_val);

                    // Bitwise and the result with 1 to zero the sign bit.
                    self.fn_builder.ins().band_imm(result, 1)
                }
                (Type::I64, Type::I64) => {
                    // Compare the i64s, returning -1 if they're equal and -0 otherwise.
                    let result = self
                        .fn_builder
                        .ins()
                        .icmp(IntCC::Equal, left_val, right_val);

                    // Bitwise and with 1 to make sure the result is either 0 or 1.
                    self.fn_builder.ins().band_imm(result, 1)
                }
                (_, _) => panic!(
                    "operands of == expression have mismatched or unsupported types {} and {}",
                    left.typ, right.typ
                ),
            },
            Operator::NotEqualTo => match (&left.typ, &right.typ) {
                (Type::Bool, Type::Bool) => {
                    // Compare the bools. This will return -1 if they're equal and -0 otherwise.
                    let result = self
                        .fn_builder
                        .ins()
                        .icmp(IntCC::NotEqual, left_val, right_val);

                    // Bitwise and the result with 1 to zero the sign bit.
                    self.fn_builder.ins().band_imm(result, 1)
                }
                (Type::I64, Type::I64) => {
                    // Compare the i64s, returning -1 if they're equal and -0 otherwise.
                    let result = self
                        .fn_builder
                        .ins()
                        .icmp(IntCC::NotEqual, left_val, right_val);

                    // Bitwise and with 1 to make sure the result is either 0 or 1.
                    self.fn_builder.ins().band_imm(result, 1)
                }
                (_, _) => panic!(
                    "operands of == expression have mismatched or unsupported types {} and {}",
                    left.typ, right.typ
                ),
            },
            Operator::GreaterThan => {
                self.fn_builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThan, left_val, right_val)
            }
            Operator::LessThan => {
                self.fn_builder
                    .ins()
                    .icmp(IntCC::SignedLessThan, left_val, right_val)
            }
            Operator::GreaterThanOrEqual => {
                self.fn_builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, left_val, right_val)
            }
            Operator::LessThanOrEqual => {
                self.fn_builder
                    .ins()
                    .icmp(IntCC::SignedLessThanOrEqual, left_val, right_val)
            }
            other => panic!("unimplemented binary operator {}", other),
        }
    }

    /// Generates IR for expressions in the function.
    fn gen_expr(&mut self, expr: &RichExpr) -> Value {
        match &expr.kind {
            RichExprKind::FunctionCall(call) => self.gen_call(call),
            RichExprKind::VariableReference(name) => self.gen_var_ref(name.to_string()),
            RichExprKind::BoolLiteral(b) => self.gen_bool_literal(*b),
            RichExprKind::I64Literal(i) => self.gen_i64_literal(*i),
            RichExprKind::BinaryOperation(left, op, right) => self.gen_binary_op(left, op, right),
            RichExprKind::UnaryOperation(op, expr) => self.gen_unary_op(op, expr),
            other => {
                panic!("unimplemented expression {}", other)
            }
        }
    }

    /// Generates IR for a function call.
    fn gen_call(&mut self, call: &RichFnCall) -> Value {
        // Attach argument types to the function signature.
        let mut sig = self.module.make_signature();
        sig.params = call.args.iter().map(|a| gen_abi_param(&a.typ)).collect();

        // Attach return type to the function signature, if one exists.
        if let Some(ret_type) = &call.ret_type {
            sig.returns.push(gen_abi_param(ret_type));
        }

        // Import the function with the matching signature from the module.
        let fn_id = self
            .module
            .declare_function(&call.fn_name, Linkage::Import, &sig)
            .expect("called function should exist");
        let fn_ref = self
            .module
            .declare_func_in_func(fn_id, self.fn_builder.func);

        // Collect passed argument values.
        let arg_vals: Vec<Value> = call.args.iter().map(|a| self.gen_expr(a)).collect();

        // Generate instructions to call the function with the collected args and return the result.
        let call = self.fn_builder.ins().call(fn_ref, arg_vals.as_slice());
        self.fn_builder.inst_results(call)[0]
    }

    /// Generates IR for a variable reference.
    fn gen_var_ref(&mut self, name: String) -> Value {
        self.fn_builder
            .use_var(self.vars.get(name.as_str()).unwrap().clone())
    }

    /// Populates the current function's signature with information from the given signature.
    fn gen_fn_sig(&mut self, sig: &FunctionSignature) {
        // Add the function argument types.
        for arg in &sig.args {
            self.fn_builder
                .func
                .signature
                .params
                .push(gen_abi_param(&arg.typ));
        }

        // Add the return type, if there is one.
        if sig.return_type.is_some() {
            self.fn_builder
                .func
                .signature
                .returns
                .push(gen_abi_param(sig.return_type.as_ref().unwrap()));
        }
    }

    /// Generates IR for the function body.
    fn gen_fn_body(&mut self, rich_fn: &RichFn) -> IRGenResult<()> {
        // Create the entry block, to start emitting code in.
        let entry_block = self.fn_builder.create_block();

        // Since this is the entry block, add block parameters corresponding to the function's
        // parameters.
        self.fn_builder
            .append_block_params_for_function_params(entry_block);

        // Tell the builder to emit code in this block.
        self.fn_builder.switch_to_block(entry_block);

        // Seal the block since nothing else can jump to it.
        self.fn_builder.seal_block(entry_block);

        // Declare and define arguments as variables so we can reference them later in function
        // body.
        for (i, arg) in rich_fn.signature.args.iter().enumerate() {
            let arg_var = self.new_var();
            self.fn_builder.declare_var(arg_var, gen_type(&arg.typ));

            let arg_val = self.fn_builder.block_params(entry_block)[i];
            self.fn_builder.def_var(arg_var, arg_val);

            self.vars.insert(arg.name.clone(), arg_var);
        }

        // Generate IR for statements.
        let mut returned = false;
        for statement in &rich_fn.closure.statements {
            if let Err(e) = self.gen_statement(statement) {
                return Err(e);
            }

            if let RichStatement::Return(_) = statement {
                returned = true
            }
        }

        // Generate a return instruction if the source code didn't already contain a return.
        if !returned {
            self.fn_builder.ins().return_(&[]);
        }

        Ok(())
    }

    /// Defines the initial value of the given variable from the given expression using the function
    /// builder.
    fn def_var(&mut self, var: Variable, expr: &RichExpr) {
        let val = self.gen_expr(expr);
        self.fn_builder.def_var(var, val);
    }

    /// Declares the type of the given variable using the function builder.
    fn declare_var(&mut self, var: Variable, typ: &Type) {
        let typ = gen_type(typ);
        self.fn_builder.declare_var(var, typ);
    }

    /// Generates an i64 literal with the given value using the function builder.
    fn gen_i64_literal(&mut self, i: i64) -> Value {
        self.fn_builder.ins().iconst(gen_type(&Type::I64), i)
    }

    /// Generates a bool literal (represented as i8 because Cranelift doesn't have bools) with the
    /// given value using the function builder.
    fn gen_bool_literal(&mut self, b: bool) -> Value {
        let val = match b {
            true => 1,
            false => 0,
        };
        self.fn_builder.ins().iconst(gen_type(&Type::Bool), val)
    }
}

/// Generates IR for a program.
pub struct IRGenerator {
    /// Stores IR generator settings.
    flags: Flags,
    /// For collecting functions and data objects and linking them together.
    module: ObjectModule,
}

impl IRGenerator {
    /// Creates a new IR generator configured for the target ISA.
    pub fn new_for_target(target_triple: &str) -> IRGenResult<Self> {
        let target_triple = match Triple::from_str(target_triple) {
            Ok(t) => t,
            Err(e) => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    format!("failed to initialize target triple: {}", e).as_str(),
                ));
            }
        };

        let isa_builder = match isa::lookup(target_triple.clone()) {
            Ok(b) => b,
            Err(e) => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    format!(
                        "failed to look up ISA builder for target {}: {}",
                        target_triple, e
                    )
                    .as_str(),
                ));
            }
        };

        IRGenerator::new_for_isa(isa_builder)
    }

    /// Creates a new IR generator configured for the host system.
    pub fn new() -> IRGenResult<Self> {
        let isa_builder = match cranelift_native::builder() {
            Ok(builder) => builder,
            Err(err) => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    format!("failed to initialize ISA builder {}", err).as_str(),
                ));
            }
        };

        IRGenerator::new_for_isa(isa_builder)
    }

    /// Creates a new IR generator from the given ISA builder.
    fn new_for_isa(isa_builder: Builder) -> IRGenResult<Self> {
        let flags = Flags::new(builder());
        let target_isa = match isa_builder.finish(flags.clone()) {
            Ok(i) => i,
            Err(e) => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    format!("failed to finish building ISA: {}", e).as_str(),
                ))
            }
        };
        debug!(
            "initializing IR generator for target {}",
            &target_isa.triple()
        );
        let obj_builder = match ObjectBuilder::new(
            target_isa,
            "program",
            cranelift_module::default_libcall_names(),
        ) {
            Ok(ob) => ob,
            Err(e) => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    format!("failed to initialize object builder: {}", e).as_str(),
                ))
            }
        };
        let module = ObjectModule::new(obj_builder);

        Ok(IRGenerator { flags, module })
    }

    /// Generates IR for the given program, returning the object product that can be used to output
    /// machine code.
    pub fn generate(mut self, prog: RichProg) -> IRGenResult<ObjectProduct> {
        // Generate IR for each statement in the program.
        for statement in &prog.statements {
            match statement {
                RichStatement::FunctionDeclaration(func) => self.gen_fn(func)?,
                // TODO: support top-level data declarations
                other => {
                    panic!("unsupported top-level statement: {}", other);
                }
            };
        }

        // Finalize all reclocations and return the compilation result.
        Ok(self.module.finish())
    }

    /// Generates IR for a new function.
    fn gen_fn(&mut self, rich_fn: &RichFn) -> IRGenResult<()> {
        // Create a new function builder that we'll use to build this function.
        let mut fn_builder_ctx = FunctionBuilderContext::new();
        let mut fn_ctx = self.module.make_context();
        let fn_gen = FnGenerator {
            vars: HashMap::new(),
            fn_builder: FunctionBuilder::new(&mut fn_ctx.func, &mut fn_builder_ctx),
            var_counter: 0,
            module: &mut self.module,
        };

        // Generate IR for the function.
        fn_gen.generate(rich_fn)?;

        // Verify the generated function IR.
        verify_function(&fn_ctx.func, &self.flags).map_err(|e| {
            IRGenError::new(IRGenErrorKind::FnVerificationFailed, e.to_string().as_str())
        })?;

        // Declare the function in the module and export it. For now, all top-level functions
        // are exported.
        let fn_id = self
            .module
            .declare_function(
                &rich_fn.signature.name,
                Linkage::Export,
                &fn_ctx.func.signature,
            )
            .map_err(|e| {
                IRGenError::new(
                    IRGenErrorKind::FnDeclarationFailed,
                    format!("error declaring function {}: {}", rich_fn.signature.name, e).as_str(),
                )
            })?;

        // Define the function to complete its compilation.
        self.module
            .define_function(fn_id, &mut fn_ctx)
            .map_err(|e| {
                IRGenError::new(
                    IRGenErrorKind::FnDeclarationFailed,
                    format!("error defining function {}: {}", rich_fn.signature.name, e).as_str(),
                )
            })?;

        debug!(
            "generated IR for function {}:\n{}",
            &rich_fn.signature.name,
            fn_ctx.func.display()
        );

        // Clear the function context since we're done with it.
        self.module.clear_context(&mut fn_ctx);

        Ok(())
    }
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
