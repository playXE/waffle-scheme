use comet::api::HeapObjectHeader;
use comet::{gc_offsetof, ConstantId};
use cranelift::codegen::ir::StackSlot;
use cranelift::prelude::{MemFlags, StackSlotData};
use cranelift::{
    codegen::ir::{self, types, FuncRef, InstBuilder},
    frontend::FunctionBuilder,
    prelude::{IntCC, JumpTableData},
};
use memoffset::offset_of;
use std::collections::{HashMap, VecDeque};

use super::*;
use crate::jit::lbc::{LBCBlock, LBCFunction};
use crate::{jit::lbc::*, Heap};
pub struct C1Translator<'a> {
    pub module: &'a JITModule,
    pub func: &'a LBCFunction,
    pub stack_slots: HashMap<u16, StackSlot>,
    pub proto: Managed<ScmPrototype>,
    pub builder: FunctionBuilder<'a>,
    pub ungenerated: VecDeque<(ir::Block, LBCBlock, Box<[Type]>)>,
    pub slowpaths: Vec<(ir::Block, LBCBlock, Box<[Type]>)>,
    pub operand_stack: Vec<(ir::Value, Type)>,
    pub env: ir::Value,
    pub frame: ir::Value,
    pub thread: ir::Value,
    pub bp: ir::Value,
    pub closure: ir::Value,
    pub trampoline: ir::Value,
    pub blocks: HashMap<LBCBlock, ir::Block>,
    pub jit_trampoline: FuncRef,
    pub close_over: FuncRef,
    pub jit_apply: FuncRef,
    pub cons: FuncRef,
    pub list: FuncRef,
    pub vector: FuncRef,
    pub current: ir::Block,
    pub end_of_block: bool,
    pub fallthrough: bool,
    pub return_block: ir::Block,
}

impl<'a> C1Translator<'a> {
    pub fn get_or_create_block(&mut self, target: LBCBlock) -> ir::Block {
        self.end_of_block = true;
        *self.blocks.entry(target).or_insert_with(|| {
            let block = self.builder.create_block();
            let mut types = vec![Type::Dynamic; self.operand_stack.len()];
            for i in 0..self.operand_stack.len() {
                let (val, cty) = self.operand_stack[i];
                types[i] = cty;
                let ty = self.builder.func.dfg.value_type(val);
                self.builder.append_block_param(block, ty);
            }
            let slowpath = self.func.blocks[target.0 as usize].slowpath;
            if slowpath {
                self.slowpaths
                    .push((block, target, types.into_boxed_slice()));
            } else {
                self.ungenerated
                    .push_back((block, target, types.into_boxed_slice()));
            }

            block
        })
    }
    pub fn generate(&mut self, entry: ir::Value) {
        let first = self.get_or_create_block(LBCBlock(0));
        self.ungenerated.pop_back().unwrap();
        // generate OSR blocks
        let mut jump_table = JumpTableData::new();
        {
            jump_table.push_entry(first);
            for bb in self.func.entrypoints.iter() {
                let ip = self.func.blocks[bb.0 as usize].entrypoint.unwrap();
                let entry = self.proto.entry_points.get_mut(&ip).unwrap();
                *entry = jump_table.len() as u32;
                let block = self.builder.create_block();
                assert!(self.blocks.insert(*bb, block).is_none());
                jump_table.push_entry(block);
            }
        }
        // setup frame variables and do branch to OSR entry
        {
            let vm_stack_off = offset_of!(SchemeThread, vm_stack);
            let frame_off = offset_of!(VMStack, current_frame);
            let frame = self.builder.ins().load(
                types::I64,
                MemFlags::new(),
                self.thread,
                vm_stack_off as i32 + frame_off as i32,
            );
            let bp = self.builder.ins().load(
                types::I64,
                MemFlags::new(),
                frame,
                offset_of!(CallFrame, bp) as i32,
            );
            let locals = self.builder.ins().load(
                types::I64,
                MemFlags::new(),
                frame,
                offset_of!(CallFrame, env) as i32,
            );
            self.env = locals;
            self.bp = bp;
            self.frame = frame;
            let closure = self.builder.ins().load(
                types::I64,
                MemFlags::new(),
                frame,
                offset_of!(CallFrame, closure) as i32,
            );
            self.closure = closure;

            let jt = self.builder.create_jump_table(jump_table);

            self.builder.ins().br_table(entry, first, jt);
        }

        {
            self.current = first;
            self.generate_from(LBCBlock(0));

            while let Some((bb, lbc, types)) = self.ungenerated.pop_front() {
                self.current = bb;
                let params = self.builder.block_params(bb);
                self.operand_stack.clear();
                self.operand_stack
                    .extend(params.iter().copied().zip(types.iter().copied()));

                self.generate_from(lbc);
            }

            self.builder.switch_to_block(self.return_block);
            let ret = self.builder.block_params(self.return_block)[0];
            self.builder.ins().return_(&[ret]);

            while let Some((bb, lbc, types)) = self.slowpaths.pop() {
                self.ungenerated.push_back((bb, lbc, types));
            }

            while let Some((bb, lbc, types)) = self.ungenerated.pop_front() {
                self.current = bb;
                let params = self.builder.block_params(bb);
                self.operand_stack.clear();
                self.operand_stack
                    .extend(params.iter().copied().zip(types.iter().copied()));

                self.generate_from(lbc);
            }
            for i in 0..self.func.entrypoints.len() {
                let block = self.blocks[&self.func.entrypoints[i]];
                self.current = block;
                self.operand_stack.clear();
                self.generate_from(self.func.entrypoints[i]);
            }
        }
    }
    pub fn generate_from(&mut self, from: LBCBlock) {
        self.builder.switch_to_block(self.current);
        let mut index = 0;
        self.end_of_block = false;
        self.fallthrough = false;

        loop {
            let code = self.func.blocks[from.0 as usize].code[index];
            index += 1;
            //  println!("{}: {}: {:?}", self.current, index - 1, code);
            match code {
                LBC::Pop => {
                    self.pop();
                }
                LBC::Is(ty) => {
                    let val = self.pop();
                    let t = self
                        .builder
                        .ins()
                        .iconst(types::I64, Value::new(true).get_raw() as i64);
                    let f = self
                        .builder
                        .ins()
                        .iconst(types::I64, Value::new(false).get_raw() as i64);
                    if val.1 == ty && ty != Type::Dynamic {
                        self.push_typed(t, Type::Bool);
                    } else if ty == Type::Dynamic {
                        self.push_typed(t, Type::Bool);
                    } else {
                        let c = self.is_type(val.0, ty);
                        let res = self.builder.ins().select(c, t, f);
                        self.push_typed(res, Type::Bool);
                    }
                }
                LBC::Imm32(x) => {
                    let imm = self
                        .builder
                        .ins()
                        .iconst(types::I64, Value::new(x).get_raw() as i64);
                    self.push(imm);
                }
                LBC::ImmFalse | LBC::ImmTrue => {
                    let imm = self.builder.ins().iconst(
                        types::I64,
                        Value::new(code == LBC::ImmTrue).get_raw() as i64,
                    );
                    self.push(imm);
                }
                LBC::ImmNull => {
                    let imm = self
                        .builder
                        .ins()
                        .iconst(types::I64, Value::new(Null).get_raw() as i64);
                    self.push(imm);
                }
                LBC::Constant(at) => {
                    let value = self.proto.constants[at as usize];
                    let val = self
                        .builder
                        .ins()
                        .iconst(types::I64, value.get_raw() as i64);
                    self.push(val);
                }
                LBC::Closure(proto) => {
                    let proto = self.proto.constants[proto as usize];
                    let proto = self
                        .builder
                        .ins()
                        .iconst(types::I64, proto.get_raw() as i64);
                    let call = self
                        .builder
                        .ins()
                        .call(self.close_over, &[self.thread, self.frame, proto]);
                    let closure = self.builder.inst_results(call)[0];
                    self.push(closure);
                }
                LBC::JumpIfNotType(cty, if_false_) => {
                    let (val, ty) = self.operand_stack.last().copied().unwrap();
                    let next = self.func.blocks[from.0 as usize].code[index];
                    match next {
                        LBC::Jump(target) => {
                            let params = self.operand_stack.iter().map(|x| x.0).collect::<Vec<_>>();
                            if ty == cty && ty != Type::Dynamic {
                                let target = self.get_or_create_block(target);
                                self.builder.ins().jump(target, &params);
                            } else if ty != cty && ty != Type::Dynamic {
                                let target = self.get_or_create_block(if_false_);
                                self.builder.ins().jump(target, &params);
                            } else {
                                let cond = self.is_type(val, cty);
                                let target1 = self.get_or_create_block(if_false_);
                                let target2 = self.get_or_create_block(target);
                                //println!("ty {} {}", target1, target2);
                                let params =
                                    self.operand_stack.iter().map(|x| x.0).collect::<Vec<_>>();
                                self.builder.ins().brnz(cond, target1, &params);
                                self.builder.ins().jump(target2, &params);
                            }
                            return;
                        }
                        _ => panic!("expected jump right after JumpIfFalse"),
                    }
                }
                LBC::JumpIfFalse(if_false_) => {
                    let next = self.func.blocks[from.0 as usize].code[index];
                    //index += 1;
                    match next {
                        LBC::Jump(target) => {
                            let value = self.pop();
                            let is_false = self.builder.ins().icmp_imm(
                                IntCC::Equal,
                                value.0,
                                Value::new(false).get_raw() as i64,
                            );
                            let is_null = self.builder.ins().icmp_imm(
                                IntCC::Equal,
                                value.0,
                                Value::new(Null).get_raw() as i64,
                            );
                            let falsey = self.builder.ins().bor(is_false, is_null);

                            let target1 = self.get_or_create_block(if_false_);
                            let target2 = self.get_or_create_block(target);
                            let params = self.operand_stack.iter().map(|x| x.0).collect::<Vec<_>>();
                            self.builder.ins().brnz(falsey, target1, &params);
                            self.builder.ins().jump(target2, &params);
                            return;
                        }
                        _ => panic!("expected jump right after JumpIfFalse"),
                    }
                }
                LBC::Jump(target) => {
                    let target = self.get_or_create_block(target);
                    let params = self.operand_stack.iter().map(|x| x.0).collect::<Vec<_>>();
                    self.builder.ins().jump(target, &params);
                    return;
                }
                LBC::Dup => self.dup(),
                LBC::Swap => self.swap(),

                LBC::Get(acc) => match acc {
                    Access::Car => {
                        let (val, _) = self.pop();
                        let ptr = self.decode_ptr(val);
                        let car = self.builder.ins().load(
                            types::I64,
                            MemFlags::new(),
                            ptr,
                            gc_offsetof!(ScmCons, car) as i32,
                        );
                        self.push(car);
                    }
                    Access::Cdr => {
                        let (val, _) = self.pop();
                        let ptr = self.decode_ptr(val);
                        let car = self.builder.ins().load(
                            types::I64,
                            MemFlags::new(),
                            ptr,
                            gc_offsetof!(ScmCons, cdr) as i32,
                        );
                        self.push(car);
                    }
                    Access::Local(local) => {
                        let val = self.builder.ins().load(
                            types::I64,
                            MemFlags::new(),
                            self.env,
                            local as i32 * 8,
                        );
                        self.push(val);
                    }
                    Access::Global(ref x) => {
                        let sym = self.proto.constants[*x as usize].downcast::<ScmSymbol>();
                        let sym = self
                            .builder
                            .ins()
                            .iconst(types::I64, unsafe { std::mem::transmute::<_, i64>(sym) });
                        let off = gc_offsetof!(ScmSymbol, value);
                        let val =
                            self.builder
                                .ins()
                                .load(types::I64, MemFlags::new(), sym, off as i32);
                        self.push(val);
                    }
                    Access::Upvalue(at) => {
                        let upvalues_offset = gc_offsetof!(Closure, upvalues);
                        let upvalues = self.builder.ins().load(
                            types::I64,
                            MemFlags::new(),
                            self.closure,
                            upvalues_offset as i32 as i32,
                        );
                        let upvalues = self
                            .builder
                            .ins()
                            .iadd_imm(upvalues, Vector::<Value, Heap>::data_offset() as i64);
                        let upval = self.builder.ins().load(
                            types::I64,
                            MemFlags::new(),
                            upvalues,
                            at as i32 * 8,
                        );

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
                        let param = self.builder.block_params(end_bb)[0];

                        self.push(param);
                    }
                    Access::Stack(at) => {
                        let ix = self.operand_stack.len() as i16 - 1 + at;
                        let val = self.operand_stack[ix as usize];
                        self.push(val.0);
                    }
                    _ => todo!(),
                },
                LBC::Set(acc) => match acc {
                    Access::Local(at) => {
                        let val = self.pop();
                        self.env_store(at, val.0)
                    }
                    Access::Upvalue(at) => {
                        let value = self.pop();
                        let upvalues_offset = gc_offsetof!(Closure, upvalues);
                        let upvalues = self.builder.ins().load(
                            types::I64,
                            MemFlags::new(),
                            self.closure,
                            upvalues_offset as i32 as i32,
                        );
                        let upvalues = self
                            .builder
                            .ins()
                            .iadd_imm(upvalues, Vector::<Value, Heap>::data_offset() as i64);
                        let upval = self.builder.ins().load(
                            types::I64,
                            MemFlags::new(),
                            upvalues,
                            at as i32 * 8,
                        );

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
                            value.0,
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

                        self.builder.ins().store(MemFlags::new(), value.0, val, 0);
                        self.builder.ins().jump(end_bb, &[]);

                        self.builder.switch_to_block(end_bb);
                    }
                    Access::Global(ref x) => {
                        let sym = self.proto.constants[*x as usize].downcast::<ScmSymbol>();
                        let sym = self
                            .builder
                            .ins()
                            .iconst(types::I64, unsafe { std::mem::transmute::<_, i64>(sym) });
                        let off = gc_offsetof!(ScmSymbol, value);
                        let val = self.pop();
                        self.builder
                            .ins()
                            .store(MemFlags::new(), val.0, sym, off as i32);
                    }
                    _ => todo!(),
                },
                LBC::Trampoline(nargs) => {
                    let function = self.pop();
                    self.store_stack();
                    let nargs_ = self.builder.ins().iconst(types::I32, nargs as i64);
                    self.builder.ins().call(
                        self.jit_trampoline,
                        &[self.thread, self.frame, function.0, nargs_],
                    );
                    self.set_si(0);
                    for _ in 0..nargs {
                        self.pop();
                    }
                    let tramp = self
                        .builder
                        .ins()
                        .iconst(types::I8, Trampoline::Call as i64);
                    self.builder
                        .ins()
                        .store(MemFlags::new(), tramp, self.trampoline, 0);
                }
                LBC::Return => {
                    let value = if self.operand_stack.is_empty() {
                        let value = self
                            .builder
                            .ins()
                            .iconst(types::I64, Value::new(Undefined).get_raw() as i64);
                        value
                    } else {
                        self.pop().0
                    };
                    self.builder.ins().jump(self.return_block, &[value]);
                    return;
                }
                LBC::ReturnUndef => {
                    let value = self
                        .builder
                        .ins()
                        .iconst(types::I64, Value::new(Undefined).get_raw() as i64);
                    self.builder.ins().jump(self.return_block, &[value]);
                    return;
                }

                LBC::Call(nargs) => {
                    let func = self.pop();
                    self.store_stack();
                    let nargs_ = self.builder.ins().iconst(types::I32, nargs as i64);

                    let call = self.builder.ins().call(
                        self.jit_apply,
                        &[self.thread, self.frame, func.0, nargs_, self.trampoline],
                    );
                    let value = self.builder.inst_results(call)[0];
                    let ok_block = self.builder.create_block();
                    let exc = self
                        .builder
                        .ins()
                        .iconst(types::I8, Trampoline::Exception as i64);
                    let res =
                        self.builder
                            .ins()
                            .load(types::I8, MemFlags::new(), self.trampoline, 0);
                    self.builder
                        .ins()
                        .br_icmp(IntCC::Equal, exc, res, self.return_block, &[value]);
                    self.builder.ins().jump(ok_block, &[]);
                    self.builder.switch_to_block(ok_block);
                    for _ in 0..nargs {
                        self.pop();
                    }
                    self.set_si(0);
                    self.push(value);
                }
                LBC::OSR(target) => {
                    let target = self.get_or_create_block(target);
                    let params = self.builder.block_params(target).len();

                    let mut stack = vec![];
                    // 1) Load values from VM stack into SSA values
                    for i in 0..params {
                        let stack_val = self.builder.ins().load(
                            types::I64,
                            MemFlags::new(),
                            self.bp,
                            i as i32 * 8,
                        );
                        stack.push(stack_val);
                    }
                    // 2) Set SI to zero so GC does not scan stack that is not really valid
                    let zero = self.builder.ins().iconst(types::I32, 0);
                    self.builder.ins().store(
                        MemFlags::new(),
                        zero,
                        self.frame,
                        offset_of!(CallFrame, si) as i32,
                    );
                    // 3) jumo to block that this OSR trampoline wanted to enter
                    self.builder.ins().jump(target, &stack);

                    return;
                }
                LBC::Hint(ty) => {
                    let (val, _) = self.pop();
                    self.push_typed(val, ty);
                }
                LBC::HintAt(at, ty) => {
                    let ix = (self.operand_stack.len() as i16 - 1 + at) as usize;
                    self.operand_stack[ix].1 = ty;
                }
                LBC::Cons => {
                    let cdr = self.pop().0;
                    let car = self.pop().0;
                    let call = self.builder.ins().call(self.cons, &[self.thread, car, cdr]);
                    let val = self.builder.inst_results(call)[0];
                    self.push_typed(val, Type::Cons);
                }
                LBC::List(argc) => {
                    let argv = self.mem_for_args(argc);
                    //let mut i = argc as i32;
                    for i in (0..argc).rev() {
                        let (val, _) = self.pop();
                        self.builder
                            .ins()
                            .store(MemFlags::new(), val, argv, i as i32 * 8);
                    }
                    let argc_ = argc;
                    let argc = self.builder.ins().iconst(types::I32, argc as i64);
                    let call = self
                        .builder
                        .ins()
                        .call(self.list, &[self.thread, argv, argc]);
                    let val = self.builder.inst_results(call)[0];
                    self.push_typed(val, if argc_ == 0 { Type::Null } else { Type::Cons });
                }
                LBC::Vector(argc) => {
                    let argv = self.mem_for_args(argc);
                    let mut i = argc as i32;

                    for (val, _) in self.operand_stack.pop() {
                        self.builder.ins().store(MemFlags::new(), val, argv, i * 8);
                        i -= 1;
                    }
                    let argc = self.builder.ins().iconst(types::I32, argc as i64);
                    let call = self
                        .builder
                        .ins()
                        .call(self.list, &[self.thread, argv, argc]);
                    let val = self.builder.inst_results(call)[0];
                    self.push_typed(val, Type::Vector);
                }

                _ => todo!(),
            }
        }
    }
    pub fn mem_for_args(&mut self, argc: u16) -> ir::Value {
        let slot = *self.stack_slots.entry(argc).or_insert_with(|| {
            let ss = StackSlotData::new(
                cranelift::prelude::StackSlotKind::ExplicitSlot,
                argc as u32 * 8,
            );
            self.builder.create_stack_slot(ss)
        });
        self.builder.ins().stack_addr(types::I64, slot, 0)
    }
    pub fn is_type(&mut self, val: ir::Value, ty: Type) -> ir::Value {
        match ty {
            Type::Int32 => self.is_int32(val),
            Type::Bool => self.is_boolean(val),
            Type::Double => self.is_double(val),
            Type::Dynamic => self.builder.ins().iconst(types::B1, 1),
            Type::Null => {
                self.builder
                    .ins()
                    .icmp_imm(IntCC::Equal, val, Value::new(Null).get_raw() as i64)
            }
            Type::Undefined => self.builder.ins().icmp_imm(
                IntCC::Equal,
                val,
                Value::new(Undefined).get_raw() as i64,
            ),
            Type::Cons => self.is_object_of(val, ConstantId::<ScmCons>::ID),
            Type::Vector => self.is_object_of(val, ConstantId::<ScmVector>::ID),
            Type::Heap(id) => self.is_object_of(val, id),
        }
    }

    pub fn is_int32(&mut self, val: ir::Value) -> ir::Value {
        #[cfg(target_pointer_width = "64")]
        {
            let x = self.builder.ins().band_imm(val, Value::NUMBER_TAG);
            self.builder
                .ins()
                .icmp_imm(IntCC::Equal, x, Value::NUMBER_TAG)
        }
    }

    pub fn is_number(&mut self, val: ir::Value) -> ir::Value {
        #[cfg(target_pointer_width = "64")]
        {
            let x = self.builder.ins().band_imm(val, Value::NUMBER_TAG);
            self.builder.ins().icmp_imm(IntCC::NotEqual, x, 0)
        }
    }

    pub fn is_double(&mut self, val: ir::Value) -> ir::Value {
        let x = self.is_number(val);
        let y = self.is_int32(val);
        let y = self.builder.ins().bnot(y);
        self.builder.ins().band(x, y)
    }

    pub fn is_pointer(&mut self, val: ir::Value) -> ir::Value {
        #[cfg(target_pointer_width = "64")]
        {
            let x = self.builder.ins().band_imm(val, Value::NOT_CELL_MASK);
            self.builder.ins().icmp_imm(IntCC::Equal, x, 0)
        }
    }

    pub fn is_boolean(&mut self, val: ir::Value) -> ir::Value {
        let x = self.builder.ins().band_imm(val, !1);
        self.builder
            .ins()
            .icmp_imm(IntCC::Equal, x, Value::VALUE_FALSE as i64)
    }
    pub fn is_false(&mut self, val: ir::Value) -> ir::Value {
        self.builder
            .ins()
            .icmp_imm(IntCC::Equal, val, Value::new(false).get_raw() as i64)
    }
    pub fn is_true(&mut self, val: ir::Value) -> ir::Value {
        self.builder
            .ins()
            .icmp_imm(IntCC::Equal, val, Value::new(true).get_raw() as i64)
    }

    pub fn encode_ptr(&mut self, val: ir::Value) -> ir::Value {
        val
    }

    pub fn is_cell_of(&mut self, val: ir::Value, type_id: u32) -> ir::Value {
        let ty = self.builder.ins().load(
            types::I32,
            MemFlags::new(),
            val,
            offset_of!(HeapObjectHeader, type_id) as i32,
        );
        self.builder
            .ins()
            .icmp_imm(IntCC::Equal, ty, type_id as i64)
    }

    pub fn is_object_of(&mut self, val: ir::Value, type_id: u32) -> ir::Value {
        let is_pointer = self.is_pointer(val);
        let then_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::B1);

        self.builder
            .ins()
            .brz(is_pointer, merge_block, &[is_pointer]);
        self.builder.ins().jump(then_block, &[]);
        self.builder.switch_to_block(then_block);
        let ptr = self.decode_ptr(val);
        let is_cell_of = self.is_cell_of(ptr, type_id);
        self.builder.ins().jump(merge_block, &[is_cell_of]);
        self.builder.switch_to_block(merge_block);
        self.builder.block_params(merge_block)[0]
    }

    pub fn store_stack(&mut self) {
        for (i, val) in self.operand_stack.iter().copied().enumerate() {
            let off = i as i32 * 8;
            self.builder
                .ins()
                .store(MemFlags::new(), val.0, self.bp, off);
        }
        self.set_si(self.operand_stack.len() as _);
    }

    pub fn set_si(&mut self, n: i32) {
        let si = self.builder.ins().iconst(types::I32, n as i64);
        self.builder.ins().store(
            MemFlags::new(),
            si,
            self.frame,
            offset_of!(CallFrame, si) as i32,
        );
    }

    pub fn env_load(&mut self, at: u16) -> ir::Value {
        self.builder
            .ins()
            .load(types::I64, MemFlags::new(), self.env, at as i32 * 8)
    }

    pub fn env_store(&mut self, at: u16, val: ir::Value) {
        self.builder
            .ins()
            .store(MemFlags::new(), val, self.env, at as i32 * 8);
    }

    pub fn decode_ptr(&mut self, val: ir::Value) -> ir::Value {
        #[cfg(target_pointer_width = "32")]
        {
            self.builder.ins().band_imm(val, Value::DATA_MASK as i64)
        }
        #[cfg(target_pointer_width = "64")]
        {
            val
        }
    }
    pub fn pop(&mut self) -> (ir::Value, Type) {
        self.operand_stack.pop().unwrap()
    }

    pub fn push(&mut self, val: ir::Value) {
        self.operand_stack.push((val, Type::Dynamic));
    }

    pub fn push_typed(&mut self, val: ir::Value, ty: Type) {
        self.operand_stack.push((val, ty));
    }

    pub fn swap(&mut self) {
        let (x, xty) = self.pop();
        let (y, yty) = self.pop();
        self.push_typed(x, xty);
        self.push_typed(y, yty);
    }

    pub fn dup(&mut self) {
        let (x, ty) = self.pop();

        self.push_typed(x, ty);
        self.push_typed(x, ty);
    }
}
