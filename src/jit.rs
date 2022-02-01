use std::mem::size_of;

use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction};
use inkwell::module::Module;
use inkwell::OptimizationLevel;

use crate::compiler::Op;
use crate::runtime::value::{ScmPrototype, ScmSymbol, Value};
use crate::runtime::SchemeThread;
use crate::Managed;

struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    execution_engine: ExecutionEngine<'ctx>,
}
