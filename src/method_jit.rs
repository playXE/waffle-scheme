use std::{mem::size_of, sync::atomic::AtomicU64};

use crate::{
    compiler::UpvalLoc,
    method_jit::lir::calling_convention,
    runtime::{
        value::{Closure, ScmPrototype, Value},
        vm::{apply, CallFrame},
        SchemeThread,
    },
    Managed,
};

pub mod lir;
pub mod lower;

#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(C)]
pub enum Trampoline {
    Return = 0,
    Call = 1,
    Exception = 2,
    Jit,
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
use capstone::arch::BuildsCapstone;
use comet_extra::alloc::vector::Vector;
use cranelift::{
    codegen::ir,
    frontend::Variable,
    prelude::{
        codegen::settings::{self, Configurable},
        types, AbiParam,
    },
};
use cranelift::{
    codegen::{self},
    frontend::FunctionBuilderContext,
};
use cranelift::{
    frontend::FunctionBuilder,
    prelude::{codegen::isa::*, Signature},
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use target_lexicon::Triple;
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
        cs.x86()
            .mode(capstone::prelude::arch::x86::ArchMode::Mode64)
            .syntax(capstone::prelude::arch::x86::ArchSyntax::Att)
            .detail(true)
            .build()
            .unwrap()
    }
}

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

pub struct MethodJIT {
    builder: FunctionBuilderContext,
    ctx: codegen::Context,
    module: JITModule,
    trampoline: FuncId,
    apply: FuncId,
    close_over: FuncId,
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

impl MethodJIT {
    pub fn new() -> Self {
        let mut builder =
            JITBuilder::with_isa(get_isa(), cranelift_module::default_libcall_names());
        builder.symbol("jit_trampoline", jit_trampoline as *const u8);
        builder.symbol("jit_apply", jit_apply as *const u8);
        builder.symbol("close_over", close_over as *const u8);
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

        Self {
            trampoline,
            apply,
            close_over,
            ctx: module.make_context(),
            module,
            builder: FunctionBuilderContext::new(),
        }
    }

    pub fn compile(
        &mut self,
        thread: &mut SchemeThread,
        proto: Managed<ScmPrototype>,
        dump: bool,
    ) -> *const u8 {
        let lir = lower::lower(thread, proto);

        {
            self.module.clear_context(&mut self.ctx);

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
            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            let params = builder.block_params(entry_block);
            let thread = params[0];
            let trampoline = params[1];
            let entry = params[2];

            let mut compiler = lir::LIRCompiler {
                module: &mut self.module,
                builder,
                jit_apply: apply,
                jit_trampoline: trampolinef,
                close_over,
                sp: Variable::with_u32(0),
                stack: vec![],
                bp: ir::Value::from_u32(1),
                frame: ir::Value::from_u32(1),
                blocks: Default::default(),
                env: ir::Value::from_u32(0),
                gen: &lir,
            };
            compiler.builder.declare_var(compiler.sp, types::I64);
            //compiler.blocks.insert(0, entry_block);
            compiler.translate(proto, thread, trampoline, entry);
            compiler.builder.seal_all_blocks();
            let name = get_jit_name(proto);

            compiler.builder.finalize();

            cranelift_preopt::optimize(&mut self.ctx, &*get_isa()).unwrap();
            if dump {
                println!(
                    "JIT: Cranelift IR for function {}: \n{}",
                    name,
                    self.ctx.func.display()
                );
            }
            let id = self
                .module
                .declare_function(
                    &name,
                    cranelift_module::Linkage::Export,
                    &self.ctx.func.signature,
                )
                .unwrap();
            self.module.define_function(id, &mut self.ctx).unwrap();

            let info = self.ctx.compile(&*get_isa()).unwrap();
            let mut code_ = vec![0; info.total_size as usize];
            unsafe {
                self.ctx.emit_to_memory(&mut code_[0]);
            }
            if true {
                // let lock = std::io::stdin();
                // let lock = lock.lock();

                //drop(lock);
            }
            self.module.clear_context(&mut self.ctx);
            self.module.finalize_definitions();
            let code = self.module.get_finalized_function(id);
            if dump {
                println!("JIT: Disassembly for function {}: ", name);

                let cs = disasm();

                let insns = cs.disasm_all(&code_, code as _);
                for ins in insns.unwrap().iter() {
                    println!("{}", ins);
                }
            }
            code
        }
    }
}
