use std::{
    collections::{BTreeSet, HashMap},
    mem::size_of,
    sync::atomic::AtomicU64,
};

use capstone::arch::{BuildsCapstone, BuildsCapstoneSyntax};
use comet::{gc_offsetof, mutator::MutatorRef};
use comet_extra::alloc::vector::Vector;
use cranelift::{
    codegen::ir::StackSlot,
    frontend::{FunctionBuilder, FunctionBuilderContext},
    prelude::{
        isa::{CallConv, TargetIsa},
        types, AbiParam, Block, InstBuilder, IntCC, MemFlags, Signature, StackSlotData,
    },
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::Module;
use memoffset::offset_of;

use crate::{
    compiler::{Op, UpvalLoc},
    runtime::{
        make_list,
        value::{Closure, Null, ScmPrototype, ScmSymbol, Upval, Upvalue, Value},
        vm::{apply, Frame},
        Runtime, SchemeThread,
    },
    Heap, Managed,
};
use cranelift::prelude::codegen;
use cranelift::prelude::codegen::ir;
use target_lexicon::Triple;
pub struct Jit {
    builder_ctx: FunctionBuilderContext,
    ctx: codegen::Context,
    module: JITModule,
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

use cranelift::prelude::codegen::settings::{self, Configurable};
fn get_isa() -> Box<dyn TargetIsa + 'static> {
    let mut flags_builder = codegen::settings::builder();
    flags_builder.set("opt_level", "speed").unwrap();
    flags_builder.set("is_pic", "false").unwrap();
    codegen::isa::lookup(Triple::host())
        .unwrap()
        .finish(settings::Flags::new(flags_builder))
}
impl Jit {
    pub fn new() -> Self {
        let mut builder =
            JITBuilder::with_isa(get_isa(), cranelift_module::default_libcall_names());
        builder.hotswap(false);
        let module = JITModule::new(builder);
        Self {
            builder_ctx: FunctionBuilderContext::new(),
            ctx: module.make_context(),
            module,
        }
    }

    pub fn compile(&mut self, prototype: Managed<ScmPrototype>, dump_jit: bool) -> *const u8 {
        if dump_jit {
            println!("Start JIT for {}", Value::new(prototype));
        }
        self.module.clear_context(&mut self.ctx);
        for _ in 0..7 {
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

        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_ctx);

        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);
        let params = builder.block_params(entry_block);
        let thread = params[0];
        let proto = params[1];
        let closure = params[2];
        let argc = params[3];
        let argv = params[4];
        let trampoline = params[5];
        let thrown = params[6];
        let mut trans = FunctionTranslator {
            builder,
            label_to_block: Default::default(),
            si: 0,
            module: &mut self.module,
            locals_offset: 0,
        };

        trans.translate(
            prototype, thread, proto, closure, argc, argv, trampoline, thrown,
        );
        let name = get_jit_name(prototype);
        if dump_jit {
            // let stdin = std::io::stdin();
            //let lock = stdin.lock();
            println!(
                "Cranelift IR for function {}: \n{}",
                name,
                trans.builder.func.display()
            );
            //drop(lock);
        }
        trans.builder.finalize();

        let id = self
            .module
            .declare_function(
                &name,
                cranelift_module::Linkage::Export,
                &self.ctx.func.signature,
            )
            .unwrap();
        self.module
            .define_function(
                id,
                &mut self.ctx,
                &mut codegen::binemit::NullTrapSink {},
                &mut codegen::binemit::NullStackMapSink {},
            )
            .unwrap();

        let mut code = vec![];
        self.ctx
            .compile_and_emit(
                &*get_isa(),
                &mut code,
                &mut codegen::binemit::NullRelocSink {},
                &mut codegen::binemit::NullTrapSink {},
                &mut codegen::binemit::NullStackMapSink {},
            )
            .unwrap();

        if dump_jit {
            // let lock = std::io::stdin();
            // let lock = lock.lock();
            println!("Disassembly for function {}: ", name);
            let cs = capstone::prelude::Capstone::new()
                .x86()
                .mode(capstone::prelude::arch::x86::ArchMode::Mode64)
                .syntax(capstone::prelude::arch::x86::ArchSyntax::Att)
                .detail(true)
                .build()
                .unwrap();

            let insns = cs.disasm_all(&code, 0x1000);
            for ins in insns.unwrap().iter() {
                println!("{}", ins);
            }
            //drop(lock);
        }
        self.module.clear_context(&mut self.ctx);
        self.module.finalize_definitions();
        let code = self.module.get_finalized_function(id);

        code
    }
}

#[allow(dead_code)]
pub struct FunctionTranslator<'a> {
    builder: FunctionBuilder<'a>,
    module: &'a mut JITModule,
    si: usize,
    locals_offset: usize,
    label_to_block: HashMap<u32, Block>,
}

unsafe extern "C" fn setup_frame(
    thread: &mut SchemeThread,
    frame: &mut Frame,
    argc: usize,
    argv: *mut Value,
) {
    frame.prev = thread.current_frame;
    thread.current_frame = frame;
    let data = frame.p.local_free_variables.as_ptr().cast::<usize>();

    for i in 0..frame.p.local_free_variable_count {
        let index = data.add(i as _).read();
        frame
            .upvalues
            .add(i as _)
            .write(Value::new(thread.mutator.allocate(
                Upvalue {
                    closed: false,
                    upval: Upval {
                        local: frame.locals.add(index as _),
                    },
                },
                comet::gc_base::AllocationSpace::New,
            )));
    }

    for i in 0..frame.p.arguments {
        if frame.p.variable_arity && i == frame.p.arguments - 1 {
            let rest = std::slice::from_raw_parts(argv, argc - i as usize);
            frame.locals.add(i as _).write(make_list(thread, rest));
            break;
        } else {
            frame.locals.add(i as _).write(argv.add(i as _).read());
        }
    }
}

unsafe extern "C" fn jit_apply(
    thread: &mut SchemeThread,
    frame: &mut Frame,
    argc: usize,
    fun: Value,
    thrown: &mut u8,
) -> Value {
    let args = std::slice::from_raw_parts(frame.stack.add(frame.si - argc as usize), argc as _);

    match apply(thread, fun, args) {
        Ok(val) => val,
        Err(val) => {
            *thrown = 1;
            return val;
        }
    }
}

unsafe extern "C" fn tail_call(
    thread: &mut SchemeThread,
    frame: &mut Frame,
    argc: usize,
    fun: Value,
) {
    thread.trampoline_arguments.clear();
    for i in 0..argc {
        thread.trampoline_arguments.push(
            frame
                .stack
                .add(frame.si - argc as usize + i as usize)
                .read(),
        );
    }
    thread.trampoline_fn = fun;
}

unsafe extern "C" fn close_over(thread: &mut SchemeThread, frame: &mut Frame, p: Value) -> Value {
    let p = p.prototype();

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
    let closure = frame.c;
    for i in 0..locations.blob_length() / size_of::<UpvalLoc>() {
        let l = locations.blob_ref::<UpvalLoc>(i);
        if l.local {
            c.upvalues
                .push(&mut thread.mutator, frame.upvalues.add(l.index as _).read());
        } else {
            c.upvalues.push(
                &mut thread.mutator,
                closure.unwrap_unchecked().upvalues[l.index as usize],
            );
        }
    }

    Value::new(c)
}

impl<'a> FunctionTranslator<'a> {
    fn get_or_create_block(&mut self, label: u32) -> Block {
        let builder = &mut self.builder;
        *self
            .label_to_block
            .entry(label)
            .or_insert_with(|| builder.create_block())
    }
    fn translate(
        &mut self,
        func: Managed<ScmPrototype>,
        thread: ir::Value,
        proto: ir::Value,
        closure: ir::Value,
        argc: ir::Value,
        argv: ir::Value,
        trampoline: ir::Value,
        thrown: ir::Value,
    ) {
        let stack_size = (func.stack_max as usize
            + func.local_free_variable_count as usize
            + func.locals as usize)
            * size_of::<Value>();

        let stack_slot = self
            .builder
            .create_stack_slot(cranelift::prelude::StackSlotData {
                kind: cranelift::prelude::StackSlotKind::ExplicitSlot,
                size: stack_size as u32,
            });
        self.locals_offset = func.stack_max as usize;
        let frame_slot = self.builder.create_stack_slot(StackSlotData {
            kind: cranelift::prelude::StackSlotKind::ExplicitSlot,
            size: size_of::<Frame>() as _,
        });

        let stack = self.builder.ins().stack_addr(types::I64, stack_slot, 0);
        let locals =
            self.builder
                .ins()
                .stack_addr(types::I64, stack_slot, (func.stack_max as i32) * 8);
        let upvalues = self.builder.ins().stack_addr(
            types::I64,
            stack_slot,
            (func.stack_max as i32 + func.locals as i32) * 8,
        );

        self.update_si(frame_slot);
        self.builder
            .ins()
            .stack_store(stack, frame_slot, offset_of!(Frame, stack) as i32);
        self.builder
            .ins()
            .stack_store(locals, frame_slot, offset_of!(Frame, locals) as i32);
        self.builder
            .ins()
            .stack_store(upvalues, frame_slot, offset_of!(Frame, upvalues) as i32);

        self.builder
            .ins()
            .stack_store(proto, frame_slot, offset_of!(Frame, p) as i32);
        self.builder
            .ins()
            .stack_store(closure, frame_slot, offset_of!(Frame, c) as i32);
        let frame = self.builder.ins().stack_addr(types::I64, frame_slot, 0);
        /*let prev = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            thread,
            offset_of!(SchemeThread, current_frame) as i32,
        );
        self.builder
            .ins()
            .stack_store(prev, frame_slot, offset_of!(Frame, prev) as i32);
        self.builder.ins().store(
            MemFlags::new(),
            frame,
            thread,
            offset_of!(SchemeThread, current_frame) as i32,
        );*/
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        let setup_sig = self.builder.import_signature(sig);
        let setup_ptr = self
            .builder
            .ins()
            .iconst(types::I64, setup_frame as usize as i64);
        self.builder
            .ins()
            .call_indirect(setup_sig, setup_ptr, &[thread, frame, argc, argv]);

        let mut apply_sig = Signature::new(CallConv::SystemV);
        apply_sig.params.push(AbiParam::new(types::I64));
        apply_sig.params.push(AbiParam::new(types::I64));
        apply_sig.params.push(AbiParam::new(types::I64));
        apply_sig.params.push(AbiParam::new(types::I64));
        apply_sig.params.push(AbiParam::new(types::I64));
        apply_sig.returns.push(AbiParam::new(types::I64));
        let apply_sig = self.builder.import_signature(apply_sig);
        let apply_ptr = self
            .builder
            .ins()
            .iconst(types::I64, jit_apply as usize as i64);

        let mut tail_sig = Signature::new(CallConv::SystemV);
        tail_sig.params.push(AbiParam::new(types::I64));
        tail_sig.params.push(AbiParam::new(types::I64));
        tail_sig.params.push(AbiParam::new(types::I64));
        tail_sig.params.push(AbiParam::new(types::I64));

        let tail_sig = self.builder.import_signature(tail_sig);
        let tail_ptr = self
            .builder
            .ins()
            .iconst(types::I64, tail_call as usize as i64);

        let mut close_sig = Signature::new(CallConv::SystemV);
        close_sig.params.push(AbiParam::new(types::I64));
        close_sig.params.push(AbiParam::new(types::I64));
        close_sig.params.push(AbiParam::new(types::I64));
        close_sig.returns.push(AbiParam::new(types::I64));
        let close_sig = self.builder.import_signature(close_sig);
        let close_ptr = self
            .builder
            .ins()
            .iconst(types::I64, close_over as usize as i64);
        let code = unsafe {
            std::slice::from_raw_parts(
                func.code.as_ptr().cast::<Op>(),
                func.code.len() / size_of::<Op>(),
            )
        };
        let label_targets = label_targets(code);
        let mut i = 0;
        let return_on_err = self.builder.create_block();
        self.builder.append_block_param(return_on_err, types::I64);

        while i < code.len() {
            if label_targets.contains(&(i as u32)) {
                let block = self.get_or_create_block(i as _);

                if !self.builder.is_filled() {
                    self.builder.ins().jump(block, &[]);
                }
                self.builder.switch_to_block(block);
            }
            match &code[i..] {
                [Op::PushFalse, ..] => {
                    let val = Value::new(false).get_raw();
                    let icons = self.builder.ins().iconst(types::I64, val as i64);
                    self.push(stack_slot, icons);
                    i += 1;
                }
                [Op::PushInt(x), ..] => {
                    let val = Value::new(*x).get_raw();
                    let icons = self.builder.ins().iconst(types::I64, val as i64);
                    self.push(stack_slot, icons);
                    i += 1;
                }
                [Op::PushConstant(x), ..] => {
                    let val = func.constants[*x as usize].get_raw();
                    let icons = self.builder.ins().iconst(types::I64, val as i64);
                    self.push(stack_slot, icons);
                    i += 1;
                }
                [Op::PushTrue, ..] => {
                    let val = Value::new(true).get_raw();
                    let icons = self.builder.ins().iconst(types::I64, val as i64);
                    self.push(stack_slot, icons);
                    i += 1;
                }
                [Op::PushNull, ..] => {
                    let val = Value::new(Null).get_raw();
                    let icons = self.builder.ins().iconst(types::I64, val as i64);
                    self.push(stack_slot, icons);
                    i += 1;
                }
                [Op::Jump(pc), ..] => {
                    let target_block = self.get_or_create_block(*pc);
                    self.builder.ins().jump(target_block, &[]);
                    i += 1;
                }
                [Op::JumpIfFalse(pc), ..] => {
                    let val = self.pop(stack_slot);
                    let cond = self.to_boolean(val);

                    let then_block = self.get_or_create_block(*pc);
                    self.builder.ins().brz(cond, then_block, &[]);
                    let block = self.builder.create_block();
                    self.builder.ins().jump(block, &[]);
                    self.builder.switch_to_block(block);
                    i += 1;
                }
                [Op::LocalGet(at), ..] => {
                    let val = self.local_get(stack_slot, *at);
                    self.push(stack_slot, val);
                    i += 1;
                }
                [Op::LocalSet(at), ..] => {
                    let val = self.pop(stack_slot);
                    self.local_set(stack_slot, *at, val);
                    i += 1;
                }
                [Op::UpvalueGet(at), ..] => {
                    /* let val = self
                    .builder
                    .ins()
                    .iconst(types::I64, Value::new(0i32).get_raw() as i64);*/
                    let val = self.upvalue_get(frame, closure, *at);
                    self.push(stack_slot, val);
                    i += 1;
                }
                [Op::UpvalueSet(at), ..] => {
                    let val = self.pop(stack_slot);
                    self.upvalue_set(closure, *at, val);
                    i += 1;
                }
                [Op::Apply(n), ..] => {
                    let fun = self.pop(stack_slot);
                    self.update_si(frame_slot);
                    for _ in 0..*n {
                        self.pop(stack_slot);
                    }
                    let argc = self.builder.ins().iconst(types::I64, *n as i64);
                    let val = self.builder.ins().call_indirect(
                        apply_sig,
                        apply_ptr,
                        &[thread, frame, argc, fun, thrown],
                    );
                    let did_throw = self
                        .builder
                        .ins()
                        .load(types::I8, MemFlags::new(), thrown, 0);
                    let next_block = self.builder.create_block();
                    let val = self.builder.inst_results(val)[0];
                    self.builder.ins().brnz(did_throw, return_on_err, &[val]);
                    self.builder.ins().jump(next_block, &[]);
                    self.builder.switch_to_block(next_block);
                    self.push(stack_slot, val);
                    i += 1;
                }
                [Op::TailApply(n), ..] => {
                    let fun = self.pop(stack_slot);
                    self.update_si(frame_slot);
                    for _ in 0..*n {
                        self.pop(stack_slot);
                    }
                    let argc = self.builder.ins().iconst(types::I64, *n as i64);
                    self.builder.ins().call_indirect(
                        tail_sig,
                        tail_ptr,
                        &[thread, frame, argc, fun],
                    );
                    let t = self.builder.ins().iconst(types::I8, 1);
                    self.builder.ins().store(MemFlags::new(), t, trampoline, 0);
                    let val = self
                        .builder
                        .ins()
                        .iconst(types::I64, Value::new(Null).get_raw() as i64);
                    self.emit_return(func, stack_slot, frame_slot, closure, thread, val);
                    let next_block = self.builder.create_block();
                    self.builder.switch_to_block(next_block);
                    i += 1;
                }
                [Op::GlobalGet, ..] => {
                    let val = self.pop(stack_slot);
                    let sym = self.decode_ptr(val);
                    let value = self.builder.ins().load(
                        types::I64,
                        MemFlags::new(),
                        sym,
                        gc_offsetof!(ScmSymbol, value) as i32,
                    );
                    self.push(stack_slot, value);
                    i += 1;
                }
                [Op::GlobalSet, ..] => {
                    let val = self.pop(stack_slot);
                    let sym = self.decode_ptr(val);
                    let val = self.pop(stack_slot);
                    self.builder.ins().store(
                        MemFlags::new(),
                        val,
                        sym,
                        gc_offsetof!(ScmSymbol, value) as i32,
                    );
                    i += 1;
                }
                [Op::Return, ..] => {
                    let val = if self.si != 0 {
                        self.pop(stack_slot)
                    } else {
                        self.builder
                            .ins()
                            .iconst(types::I64, Value::encode_undefined_value().get_raw() as i64)
                    };
                    self.emit_return(func, stack_slot, frame_slot, closure, thread, val);
                    i += 1;
                }

                [Op::CloseOver, ..] => {
                    let fun = self.pop(stack_slot);
                    let inst = self.builder.ins().call_indirect(
                        close_sig,
                        close_ptr,
                        &[thread, frame, fun],
                    );
                    let res = self.builder.inst_results(inst)[0];
                    self.push(stack_slot, res);
                    i += 1;
                }
                _ => unreachable!(),
            }
            /* if !self.builder.is_filled() {
                let val = self
                    .builder
                    .ins()
                    .iconst(types::I64, Value::new(Null).get_raw() as i64);
                self.builder.ins().jump(return_on_err, &[val]);
            }*/
        }
        //self.builder.seal_all_blocks();
        self.builder.switch_to_block(return_on_err);
        let param = self.builder.block_params(return_on_err)[0];
        self.emit_return(func, stack_slot, frame_slot, closure, thread, param);
        self.builder.seal_all_blocks();
    }

    fn emit_return(
        &mut self,
        proto: Managed<ScmPrototype>,
        stack: StackSlot,
        frame: StackSlot,
        closure: ir::Value,
        thread: ir::Value,
        val: ir::Value,
    ) {
        let _ = closure;
        for i in 0..proto.local_free_variable_count {
            self.upvalue_close(proto, stack, i)
        }

        let prev = self
            .builder
            .ins()
            .stack_load(types::I64, frame, offset_of!(Frame, prev) as i32);
        self.builder.ins().store(
            MemFlags::new(),
            prev,
            thread,
            offset_of!(SchemeThread, current_frame) as i32,
        );
        self.builder.ins().return_(&[val]);
    }

    fn to_boolean(&mut self, val: ir::Value) -> ir::Value {
        let null = Value::new(Null);
        let is_null = self
            .builder
            .ins()
            .icmp_imm(IntCC::NotEqual, val, null.get_raw() as i64);
        let is_false =
            self.builder
                .ins()
                .icmp_imm(IntCC::NotEqual, val, Value::new(false).get_raw() as i64);
        self.builder.ins().band(is_null, is_false)
    }

    fn push(&mut self, stack: StackSlot, val: ir::Value) {
        self.builder
            .ins()
            .stack_store(val, stack, self.si as i32 * 8);
        self.si += 1;
    }
    fn pop(&mut self, stack: StackSlot) -> ir::Value {
        self.si -= 1;
        self.builder
            .ins()
            .stack_load(types::I64, stack, self.si as i32 * 8)
    }
    fn local_set(&mut self, stack: StackSlot, at: u16, val: ir::Value) {
        self.builder
            .ins()
            .stack_store(val, stack, (self.locals_offset as i32 + at as i32) * 8);
    }

    fn local_get(&mut self, stack: StackSlot, at: u16) -> ir::Value {
        self.builder.ins().stack_load(
            types::I64,
            stack,
            (self.locals_offset as i32 + at as i32) * 8,
        )
    }
    fn upvalue_get(&mut self, frame: ir::Value, closure: ir::Value, at: u16) -> ir::Value {
        let _ = frame;
        /*let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        let sig = self.builder.import_signature(sig);
        let f = self.builder.ins().iconst(types::I64, debug as i64);
        */
        let upvalues_offset = gc_offsetof!(Closure, upvalues);
        let upvalues =
            self.builder
                .ins()
                .load(types::I64, MemFlags::new(), closure, upvalues_offset as i32);
        let data = self
            .builder
            .ins()
            .iadd_imm(upvalues, Vector::<Value, Heap>::data_offset() as i64);
        //self.builder.ins().call_indirect(sig, f, &[frame, data]);
        let upval = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), data, at as i32 * 8);
        //println!("at {}", at * 8);

        let upval = self.decode_ptr(upval);
        let is_closed = self.builder.ins().load(
            types::I8,
            MemFlags::new(),
            upval,
            gc_offsetof!(Upvalue, closed) as i32,
        );
        let converted_bb = self.builder.create_block();
        let local_bb = self.builder.create_block();
        let end_bb = self.builder.create_block();
        self.builder.append_block_param(end_bb, types::I64);
        self.builder.ins().brz(is_closed, local_bb, &[]);
        self.builder.ins().jump(converted_bb, &[]);
        self.builder.switch_to_block(converted_bb);
        let val = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            upval,
            gc_offsetof!(Upvalue, upval.converted) as i32,
        );
        self.builder.ins().jump(end_bb, &[val]);
        self.builder.switch_to_block(local_bb);
        let val = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            upval,
            gc_offsetof!(Upvalue, upval.local) as i32,
        );

        let val = self.builder.ins().load(types::I64, MemFlags::new(), val, 0);
        self.builder.ins().jump(end_bb, &[val]);

        self.builder.switch_to_block(end_bb);
        let params = self.builder.block_params(end_bb);

        params[0]
    }

    fn upvalue_set(&mut self, closure: ir::Value, at: u16, value: ir::Value) {
        let upvalues_offset = gc_offsetof!(Closure, upvalues);
        let upvalues =
            self.builder
                .ins()
                .load(types::I64, MemFlags::new(), closure, upvalues_offset as i32);
        let data = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            upvalues,
            Vector::<Value, Heap>::data_offset() as i32,
        );
        let upval = self.builder.ins().iadd_imm(data, at as i64 * 8);
        let upval = self.decode_ptr(upval);
        let is_closed = self.builder.ins().load(
            types::I8,
            MemFlags::new(),
            upval,
            gc_offsetof!(Upvalue, closed) as i32,
        );
        let converted_bb = self.builder.create_block();
        let local_bb = self.builder.create_block();
        let end_bb = self.builder.create_block();

        self.builder.ins().brz(is_closed, local_bb, &[]);
        self.builder.ins().jump(converted_bb, &[]);
        self.builder.switch_to_block(converted_bb);
        self.builder.ins().store(
            MemFlags::new(),
            value,
            upval,
            gc_offsetof!(Upvalue, upval.converted) as i32,
        );
        self.builder.ins().jump(end_bb, &[]);
        self.builder.switch_to_block(local_bb);
        let val = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            upval,
            gc_offsetof!(Upvalue, upval.local) as i32,
        );

        self.builder.ins().store(MemFlags::new(), value, val, 0);
        self.builder.ins().jump(end_bb, &[]);

        self.builder.switch_to_block(end_bb);
    }

    fn upvalue_close(&mut self, proto: Managed<ScmPrototype>, stack: StackSlot, at: u16) {
        /*let upvalues_offset = gc_offsetof!(Closure, upvalues);
        let upvalues =
            self.builder
                .ins()
                .load(types::I64, MemFlags::new(), closure, upvalues_offset as i32);
        let data = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            upvalues,
            Vector::<Value, Heap>::data_offset() as i32,
        );*/
        let upval_offset = (proto.stack_max as i32 + proto.locals as i32 + at as i32) * 8;

        let upval = self
            .builder
            .ins()
            .stack_load(types::I64, stack, upval_offset);
        let upval = self.decode_ptr(upval);

        let c = self.builder.ins().iconst(types::I8, 1);
        self.builder.ins().store(
            MemFlags::new(),
            c,
            upval,
            gc_offsetof!(Upvalue, closed) as i32,
        );
        let local = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            upval,
            gc_offsetof!(Upvalue, upval.local) as i32,
        );
        let value = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), local, 0);
        self.builder.ins().store(
            MemFlags::new(),
            value,
            upval,
            gc_offsetof!(Upvalue, upval.converted) as i32,
        );
    }

    fn decode_ptr(&mut self, val: ir::Value) -> ir::Value {
        self.builder.ins().band_imm(val, Value::DATA_MASK as i64)
    }
    fn update_si(&mut self, frame: StackSlot) {
        let si = self.builder.ins().iconst(types::I64, self.si as i64);
        self.builder
            .ins()
            .stack_store(si, frame, offset_of!(Frame, si) as i32);
    }
}

fn label_targets(code: &[Op]) -> BTreeSet<u32> {
    let mut targets = BTreeSet::new();
    for ins in code {
        match ins {
            Op::Jump(t) | Op::JumpIfFalse(t) => {
                targets.insert(*t);
            }
            _ => (),
        }
    }
    targets
}

pub(crate) fn compile_thread(mutator: MutatorRef<Heap>, runtime: Runtime) {
    let inner = runtime.inner();
    while !inner
        .compile_thread_terminating
        .load(std::sync::atomic::Ordering::Relaxed)
    {
        let mut guard = inner.compile_queue.lock();
        mutator.safepoint();
        let state = mutator.enter_unsafe();
        inner.compile_queue_wake.wait(&mut guard);
        drop(state);
        while let Some(func) = guard.pop() {
            if func
                .jit_code
                .load(std::sync::atomic::Ordering::Relaxed)
                .is_null()
            {
                let code = inner.jit.compile(func, inner.dump_jit);
                func.jit_code
                    .store(code as _, std::sync::atomic::Ordering::Relaxed);
            }
        }
    }
}
