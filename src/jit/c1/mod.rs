use std::collections::HashMap;
use std::sync::atomic::AtomicU64;

use capstone::arch::BuildsCapstone;
use codegen::settings::{self, Configurable};
use cranelift::codegen::{self, ir, ir::types};
use cranelift::frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift::prelude::isa::TargetIsa;
use cranelift::prelude::{AbiParam, Signature};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::FuncId;
use cranelift_module::{Linkage, Module};
use target_lexicon::Triple;

use crate::compiler::{Op, UpvalLoc};
use crate::jit::Trampoline;
use crate::runtime::value::*;
use crate::runtime::vm::*;
use crate::runtime::*;
use crate::Managed;
use comet_extra::alloc::vector::Vector;
use std::mem::size_of;

pub mod translate;

pub unsafe extern "C" fn close_over(
    thread: &mut SchemeThread,
    frame: &mut CallFrame,
    proto: Value,
) -> Value {
    let p = proto.downcast::<ScmPrototype>();
    let locations = Value::new(p.upvalues);
    let upvalues = Vector::with_capacity(
        &mut thread.mutator,
        locations.blob_length() / size_of::<UpvalLoc>(),
    );

    let mut c = thread.mutator.allocate(
        Closure {
            prototype: p,
            upvalues,
        },
        comet::gc_base::AllocationSpace::New,
    );
    let n = locations.blob_length() / size_of::<UpvalLoc>();
    for i in 0..n {
        let l = locations.blob_ref::<UpvalLoc>(i);
        if l.local {
            assert!(frame.upvalues > frame.bp.add(frame.si));
            c.upvalues
                .push(&mut thread.mutator, frame.upvalues.add(l.index as _).read());
        } else {
            c.upvalues.push(
                &mut thread.mutator,
                frame.closure.unwrap_unchecked().upvalues[l.index as usize],
            )
        }
    }
    Value::new(c)
}
pub type JITSig =
    extern "C" fn(&mut SchemeThread, trampoline: &mut Trampoline, entry_ip: usize) -> Value;

pub extern "C" fn jit_trampoline(
    thread: &mut SchemeThread,
    frame: &mut CallFrame,
    func: Value,
    nargs: u32,
) {
    thread.trampoline_fn = func;
    thread.trampoline_arguments.clear();
    thread
        .trampoline_arguments
        .extend_from_slice(unsafe { frame.slice(nargs as _) });
    for _ in 0..nargs {
        unsafe {
            frame.pop();
        }
    }
}

pub extern "C" fn jit_apply(
    thread: &mut SchemeThread,
    frame: &mut CallFrame,
    func: Value,
    nargs: u32,
    res: &mut Trampoline,
) -> Value {
    let val = match apply(thread, func, unsafe { frame.slice(nargs as usize) }) {
        Ok(val) => val,
        Err(e) => {
            *res = Trampoline::Exception;
            e
        }
    };

    for _ in 0..nargs {
        unsafe {
            frame.pop();
        }
    }
    val
}
fn get_isa() -> Box<dyn TargetIsa + 'static> {
    let mut flags_builder = codegen::settings::builder();
    flags_builder.set("opt_level", "speed").unwrap();
    flags_builder.set("is_pic", "false").unwrap();
    codegen::isa::lookup(Triple::host())
        .unwrap()
        .finish(settings::Flags::new(flags_builder))
}

fn disasm() -> capstone::Capstone {
    let cs = capstone::prelude::Capstone::new();
    #[cfg(target_arch = "aarch64")]
    {
        let mut cs = cs
            .arm64()
            .mode(capstone::prelude::arch::arm64::ArchMode::Arm)
            .detail(true)
            .build()
            .unwrap();
        cs.set_skipdata(true).unwrap();
        cs
    }
    #[cfg(target_arch = "x86_64")]
    {
        use capstone::arch::BuildsCapstoneSyntax;

        cs.x86()
            .mode(capstone::prelude::arch::x86::ArchMode::Mode64)
            .syntax(capstone::prelude::arch::x86::ArchSyntax::Att)
            .detail(true)
            .build()
            .unwrap()
    }
}

const TRIPLE: Triple = Triple::host();
use codegen::isa;

use self::translate::C1Translator;

use super::bc2lbc::BC2LBC;

pub fn calling_convention() -> isa::CallConv {
    isa::CallConv::triple_default(&TRIPLE)
}

#[allow(dead_code)]
pub struct C1JIT {
    builder: FunctionBuilderContext,
    ctx: codegen::Context,
    module: JITModule,
    isa: Box<dyn TargetIsa>,
    trampoline: FuncId,
    apply: FuncId,
    close_over: FuncId,
    cons: FuncId,
    list: FuncId,
    vector: FuncId,
}

impl C1JIT {
    pub fn new() -> Self {
        let mut builder =
            JITBuilder::with_isa(get_isa(), cranelift_module::default_libcall_names());
        builder.symbol("jit_trampoline", jit_trampoline as *const u8);
        builder.symbol("jit_apply", jit_apply as *const u8);
        builder.symbol("close_over", close_over as *const u8);
        builder.symbol("list", super::list as _);
        builder.symbol("vector", super::vector as _);
        builder.symbol("cons", super::cons as _);
        builder.hotswap(false);
        let mut module = JITModule::new(builder);
        let trampoline = {
            let mut trampoline = Signature::new(calling_convention());
            trampoline.params.push(AbiParam::new(types::I64));
            trampoline.params.push(AbiParam::new(types::I64));
            trampoline.params.push(AbiParam::new(types::I64));
            trampoline.params.push(AbiParam::new(types::I32));
            module
                .declare_function("jit_trampoline", Linkage::Import, &trampoline)
                .unwrap()
        };
        let apply = {
            let mut apply = Signature::new(calling_convention());
            apply.params.push(AbiParam::new(types::I64));
            apply.params.push(AbiParam::new(types::I64));
            apply.params.push(AbiParam::new(types::I64));
            apply.params.push(AbiParam::new(types::I32));
            apply.params.push(AbiParam::new(types::I64));
            apply.returns.push(AbiParam::new(types::I64));
            module
                .declare_function("jit_apply", Linkage::Import, &apply)
                .unwrap()
        };

        let close_over = {
            let mut close_over = Signature::new(calling_convention());
            close_over.params.push(AbiParam::new(types::I64));
            close_over.params.push(AbiParam::new(types::I64));
            close_over.params.push(AbiParam::new(types::I64));
            close_over.returns.push(AbiParam::new(types::I64));
            module
                .declare_function("close_over", Linkage::Import, &close_over)
                .unwrap()
        };
        let cons = {
            let mut cons = Signature::new(calling_convention());
            cons.params.push(AbiParam::new(types::I64));
            cons.params.push(AbiParam::new(types::I64));
            cons.params.push(AbiParam::new(types::I64));
            cons.returns.push(AbiParam::new(types::I64));
            module
                .declare_function("cons", Linkage::Import, &cons)
                .unwrap()
        };

        let list = {
            let mut cons = Signature::new(calling_convention());
            cons.params.push(AbiParam::new(types::I64));
            cons.params.push(AbiParam::new(types::I64));
            cons.params.push(AbiParam::new(types::I32));
            cons.returns.push(AbiParam::new(types::I64));
            module
                .declare_function("list", Linkage::Import, &cons)
                .unwrap()
        };

        let vector = {
            let mut cons = Signature::new(calling_convention());
            cons.params.push(AbiParam::new(types::I64));
            cons.params.push(AbiParam::new(types::I64));
            cons.params.push(AbiParam::new(types::I32));
            cons.returns.push(AbiParam::new(types::I64));
            module
                .declare_function("vector", Linkage::Import, &cons)
                .unwrap()
        };
        Self {
            trampoline,
            cons,
            list,
            vector,
            apply,
            close_over,
            ctx: module.make_context(),
            module,
            builder: FunctionBuilderContext::new(),
            isa: get_isa(),
        }
    }
    #[allow(unused_variables)]
    pub fn compile(
        &mut self,
        thread: &mut SchemeThread,
        proto: Managed<ScmPrototype>,
        dump_jit: bool,
        dump_disassembly: bool,
    ) -> *mut u8 {
        let code = proto.code.as_ptr();
        let len = proto.code.len() / size_of::<Op>();
        let code = unsafe { std::slice::from_raw_parts::<Op>(code.cast::<Op>(), len) };

        let lbc = BC2LBC::new(proto, code).generate();

        if dump_jit {
            println!("low-level bytecode for {}: ", Value::new(proto));
            println!("{}", lbc.display());
        }
        {
            for _ in 0..3 {
                self.ctx
                    .func
                    .signature
                    .params
                    .push(AbiParam::new(types::I64));
            }
            self.ctx
                .func
                .signature
                .returns
                .push(AbiParam::new(types::I64));

            let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder);
            let apply = self
                .module
                .declare_func_in_func(self.apply, &mut builder.func);
            let trampolinef = self
                .module
                .declare_func_in_func(self.trampoline, &mut builder.func);
            let close_over = self
                .module
                .declare_func_in_func(self.close_over, &mut builder.func);

            let cons = self
                .module
                .declare_func_in_func(self.cons, &mut builder.func);
            let list = self
                .module
                .declare_func_in_func(self.list, &mut builder.func);
            let vector = self
                .module
                .declare_func_in_func(self.vector, &mut builder.func);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            let params = builder.block_params(entry_block);
            let thread = params[0];
            let trampoline = params[1];
            let entry = params[2];
            let return_block = builder.create_block();
            builder.append_block_param(return_block, types::I64);

            let mut compiler = C1Translator {
                module: &self.module,
                builder,
                slowpaths: vec![],
                stack_slots: HashMap::new(),
                func: &lbc,
                proto,
                jit_apply: apply,
                jit_trampoline: trampolinef,
                close_over,
                bp: ir::Value::from_u32(0),
                frame: ir::Value::from_u32(0),
                trampoline,
                thread,
                fallthrough: false,
                end_of_block: false,
                operand_stack: vec![],
                env: ir::Value::from_u32(0),
                closure: ir::Value::from_u32(0),
                return_block,
                current: ir::Block::from_u32(0),
                blocks: Default::default(),
                ungenerated: Default::default(),
                vector,
                cons,
                list,
            };

            compiler.generate(entry);

            compiler.builder.seal_all_blocks();

            compiler.builder.finalize();

            cranelift_preopt::optimize(&mut self.ctx, &*get_isa()).unwrap();

            if dump_jit {
                println!("Cranelift IR for {}:", Value::new(proto));
                println!("{}", self.ctx.func.display());
            }
            let info = self.ctx.compile(&*get_isa()).unwrap();
            let mut code_ = vec![0; info.total_size as usize];
            unsafe {
                self.ctx.emit_to_memory(&mut code_[0]);
            }

            let name = get_jit_name(proto);
            let id = self
                .module
                .declare_function(&name, Linkage::Export, &self.ctx.func.signature)
                .unwrap();
            self.module.define_function(id, &mut self.ctx).unwrap();
            self.module.clear_context(&mut self.ctx);
            self.module.finalize_definitions();
            let code = self.module.get_finalized_function(id);
            if dump_disassembly {
                println!("disassembly for {}", Value::new(proto));

                let cs = disasm();

                let insns = cs.disasm_all(&code_, code as _);
                for ins in insns.unwrap().iter() {
                    println!("{}", ins);
                }
            }

            proto
                .jit_code
                .store(code as _, std::sync::atomic::Ordering::Release);
            code as *mut u8
        }
    }
}

static ID: AtomicU64 = AtomicU64::new(0);

fn get_jit_name(f: Managed<ScmPrototype>) -> String {
    match f.name {
        Some(name) => format!(
            "{}(jit-{})",
            name.string,
            ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ),
        None => {
            format!(
                "jit-{}",
                ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
            )
        }
    }
}
