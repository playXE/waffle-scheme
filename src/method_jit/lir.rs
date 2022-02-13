use std::collections::BTreeMap;

use crate::{
    runtime::{
        value::{
            Closure, Null, ScmCons, ScmPrototype, ScmSymbol, Undefined, Upvalue, Value, INT32_TAG,
            OBJECT_TAG,
        },
        vm::{CallFrame, VMStack},
        SchemeThread,
    },
    Heap, Managed,
};

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Lir {
    Car,
    Cdr,
    VectorRef,
    VectorSet,
    Floor,
    Round,
    Sin,
    Cos,
    IBin(Bin),
    FBin(Bin),

    Constant(u32),
    Int32(i32),
    T,
    F,
    N,
    LocalGet(u16),
    LocalSet(u16),
    UpvalueGet(u16),
    UpvalueSet(u16),
    GlobalGet(u32),
    GlobalSet(u32),
    IsCell(u32),
    JumpNotInt(u32),
    JumpNoFloat(u32),
    JumpNotNull(u32),
    JumpNotUndefined(u32),
    JumpNotObject(u32),
    JumpInt(u32),
    JumpFloat(u32),
    JumpObject(u32),
    JumpCellOf(u32, u32),
    JumpNotCellOf(u32, u32),
    ToBoolean,
    Jump(u32),
    JumpIfFalse(u32),
    Swap,
    CloseOver(u32),
    Apply(u16),
    Trampoline(u16),
    Ret,
    RetUndef,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Bin {
    Add,
    Sub,
    Div,
    Mul,
    Rem,
    Eq,
    Gt,
    Ge,
    Le,
    Lt,
}

impl std::fmt::Display for Bin {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Add => write!(fmt, "add"),
            Self::Sub => write!(fmt, "sub"),
            Self::Div => write!(fmt, "div"),
            Self::Mul => write!(fmt, "mul"),
            Self::Rem => write!(fmt, "rem"),
            Self::Eq => write!(fmt, "eq"),
            Self::Gt => write!(fmt, "gt"),
            Self::Ge => write!(fmt, "ge"),
            Self::Le => write!(fmt, "le"),
            Self::Lt => write!(fmt, "lt"),
        }
    }
}

pub struct BasicBlock {
    id: u32,
    code: Vec<Lir>,
}

pub struct LIRGen {
    pub(crate) blocks: Vec<BasicBlock>,
    current: Option<u32>,
}

impl LIRGen {
    pub fn new() -> Self {
        Self {
            blocks: Vec::with_capacity(1),
            current: None,
        }
    }
    pub fn is_filled(&self) -> bool {
        self.current.is_none() || {
            let block = &self.blocks[self.current.unwrap() as usize];
            let last = block.code.last();
            match last {
                Some(lir) => match lir {
                    Lir::Jump(_) | Lir::Ret => true,
                    _ => false,
                },
                _ => false,
            }
        }
    }
    pub fn new_block(&mut self) -> u32 {
        let id = self.blocks.len() as u32;
        self.blocks.push(BasicBlock { id, code: vec![] });

        id
    }

    pub fn switch_to_block(&mut self, block: u32) {
        self.current = Some(block);
    }

    pub fn emit(&mut self, ins: Lir) {
        let id = self.current.expect("no basic block present");
        self.blocks[id as usize].code.push(ins);
    }

    pub fn display<'a>(&'a self, proto: Managed<ScmPrototype>) -> LIRDisplay<'a> {
        LIRDisplay {
            blocks: &self.blocks,
            proto,
        }
    }

    pub fn compile(&self) {}
}

pub struct LIRDisplay<'a> {
    blocks: &'a [BasicBlock],
    proto: Managed<ScmPrototype>,
}

impl<'a> std::fmt::Display for LIRDisplay<'a> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(fmt, "LIR for {}:", Value::new(self.proto))?;
        for block in self.blocks {
            let id = block.id;
            writeln!(fmt, " block.{}: ", id)?;

            for lir in block.code.iter() {
                write!(fmt, "  ")?;
                match lir {
                    Lir::IBin(x) => {
                        writeln!(fmt, "i32.{}", x.to_string().to_lowercase())?;
                    }
                    Lir::FBin(x) => {
                        writeln!(fmt, "f64.{}", x.to_string().to_lowercase())?;
                    }
                    Lir::Car => writeln!(fmt, "car")?,
                    Lir::Cdr => writeln!(fmt, "cdr")?,
                    Lir::Int32(x) => writeln!(fmt, "i32 {}", x)?,
                    Lir::Constant(x) => {
                        writeln!(
                            fmt,
                            "get.const %{} ({})",
                            x, self.proto.constants[*x as usize],
                        )?;
                    }
                    Lir::F => writeln!(fmt, "false")?,
                    Lir::T => writeln!(fmt, "true")?,
                    Lir::N => writeln!(fmt, "null")?,
                    Lir::IsCell(x) => writeln!(fmt, "is_cell {:x}", x)?,

                    Lir::Jump(x) => writeln!(fmt, "jump block.{}", x)?,
                    Lir::JumpIfFalse(x) => writeln!(fmt, "jump_if_false block.{}", x)?,
                    Lir::Trampoline(x) => writeln!(fmt, "trampoline {}", x)?,
                    Lir::Ret => writeln!(fmt, "ret")?,
                    Lir::RetUndef => writeln!(fmt, "retundef")?,
                    Lir::LocalGet(x) => writeln!(fmt, "get.local %{}", x)?,
                    Lir::LocalSet(x) => writeln!(fmt, "set.local %{}", x)?,
                    Lir::UpvalueGet(x) => writeln!(fmt, "get.upvalue %{}", x)?,
                    Lir::UpvalueSet(x) => writeln!(fmt, "set.upvalue %{}", x)?,
                    Lir::GlobalGet(x) => {
                        writeln!(
                            fmt,
                            "get.global %{} ({})",
                            x, self.proto.constants[*x as usize]
                        )?;
                    }
                    Lir::GlobalSet(x) => writeln!(
                        fmt,
                        "set.global %{} ({})",
                        x, self.proto.constants[*x as usize]
                    )?,
                    Lir::ToBoolean => {
                        writeln!(fmt, "to_boolean")?;
                    }
                    Lir::Apply(x) => writeln!(fmt, "apply {}", x)?,
                    Lir::CloseOver(x) => writeln!(
                        fmt,
                        "make_closure %{} ({})",
                        x, self.proto.constants[*x as usize]
                    )?,
                    x => write!(fmt, "{:?}", x)?,
                }
            }
        }

        writeln!(fmt, "")
    }
}

use comet::{api::HeapObjectHeader, gc_offsetof};
use comet_extra::alloc::vector::Vector;
use cranelift::{
    codegen::ir::{self, types, FuncRef, InstBuilder},
    frontend::FunctionBuilder,
    prelude::{IntCC, Variable},
};
use cranelift::{codegen::isa, prelude::MemFlags};
use cranelift_jit::JITModule;
use memoffset::offset_of;
use target_lexicon::Triple;

use super::Trampoline;

const TRIPLE: Triple = Triple::host();

pub fn calling_convention() -> isa::CallConv {
    isa::CallConv::triple_default(&TRIPLE)
}

pub struct LIRCompiler<'a> {
    pub gen: &'a LIRGen,
    pub builder: FunctionBuilder<'a>,
    pub module: &'a mut JITModule,
    pub bp: ir::Value,
    pub frame: ir::Value,
    pub si: Variable,
    pub env: ir::Value,
    pub blocks: BTreeMap<u32, ir::Block>,
    pub jit_trampoline: FuncRef,
    pub close_over: FuncRef,
    pub jit_apply: FuncRef,
}

impl<'a> LIRCompiler<'a> {
    pub fn translate(
        &mut self,
        proto: Managed<ScmPrototype>,
        thread: ir::Value,
        trampoline: ir::Value,
    ) {
        // Setup variables
        let vm_stack_off = offset_of!(SchemeThread, vm_stack);
        let frame_off = offset_of!(VMStack, current_frame);
        let frame = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            thread,
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
        let si = self.builder.ins().iconst(types::I64, 0);
        self.builder.def_var(self.si, si);
        let closure = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            frame,
            offset_of!(CallFrame, closure) as i32,
        );
        // map LIR blocks to Cranelift IR blocks
        //
        // note that first block with id 0 is entry block and it is already in blocks map.
        for block in self.gen.blocks.iter().skip(1) {
            let bb = self.builder.create_block();
            self.blocks.insert(block.id, bb);
        }
        let return_block = self.builder.create_block();
        self.builder.append_block_param(return_block, types::I64);
        // emit Cranelift IR from LIR
        for lir_block in self.gen.blocks.iter() {
            let block = self.blocks.get(&lir_block.id).copied().unwrap();
            if self.builder.current_block() != Some(block) {
                self.builder.switch_to_block(block);
            }

            for node in lir_block.code.iter() {
                match node {
                    Lir::Swap => {
                        let x = self.pop();
                        let y = self.pop();
                        self.push(x);
                        self.push(y);
                    }
                    Lir::Car => {
                        let value = self.pop();
                        let cons = self.decode_ptr(value);
                        let car_off = gc_offsetof!(ScmCons, car);
                        let car = self.builder.ins().load(
                            types::I64,
                            MemFlags::new(),
                            cons,
                            car_off as i32,
                        );
                        self.push(car);
                    }
                    Lir::JumpNotCellOf(id, target) => {
                        let target = self.blocks.get(target).copied().unwrap();
                        let value = self.top();
                        let is_pointer = self.is_pointer(value);
                        let is_pointer_block = self.builder.create_block();
                        self.builder.ins().brz(is_pointer, target, &[]);
                        self.builder.ins().jump(is_pointer_block, &[]);
                        self.builder.switch_to_block(is_pointer_block);
                        let ptr = self.decode_ptr(value);
                        let type_id = self.builder.ins().load(
                            types::I32,
                            MemFlags::new(),
                            ptr,
                            offset_of!(HeapObjectHeader, type_id) as i32,
                        );
                        let cell_id = self.builder.ins().iconst(types::I32, *id as i64);
                        self.builder
                            .ins()
                            .br_icmp(IntCC::NotEqual, type_id, cell_id, target, &[]);
                        let next_block = self.builder.create_block();
                        self.builder.ins().jump(next_block, &[]);
                        self.builder.switch_to_block(next_block);
                    }
                    Lir::JumpNotInt(x) => {
                        let value = self.top();
                        let is_int = self.is_int(value);
                        let target = self.blocks.get(x).copied().unwrap();
                        self.builder.ins().brz(is_int, target, &[]);
                        let next = self.builder.create_block();
                        self.builder.ins().jump(next, &[]);
                        self.builder.switch_to_block(next);
                    }
                    Lir::Jump(x) => {
                        let target = self.blocks.get(x).copied().unwrap();
                        self.builder.ins().jump(target, &[]);
                    }
                    Lir::JumpIfFalse(x) => {
                        let target = self.blocks.get(x).copied().unwrap();
                        let value = self.pop();
                        let is_falsey = self.is_false_or_null(value);
                        self.builder.ins().brnz(is_falsey, target, &[]);
                    }
                    Lir::LocalGet(at) => {
                        let value = self.env_load(*at);
                        self.push(value);
                    }
                    Lir::LocalSet(at) => {
                        let value = self.pop();
                        self.env_store(*at, value);
                    }
                    Lir::Ret => {
                        let value = self.pop_or_undef();
                        self.builder.ins().return_(&[value]);
                    }
                    Lir::RetUndef => {
                        let value = self
                            .builder
                            .ins()
                            .iconst(types::I64, Value::new(Undefined).get_raw() as i64);
                        self.builder.ins().return_(&[value]);
                    }
                    Lir::Trampoline(nargs) => {
                        let func = self.pop();
                        self.update_frame();
                        let nargs = self.builder.ins().iconst(types::I32, *nargs as i64);
                        self.builder
                            .ins()
                            .call(self.jit_trampoline, &[thread, self.frame, func, nargs]);
                        let t = self
                            .builder
                            .ins()
                            .iconst(types::I8, Trampoline::Call as i64);
                        self.builder.ins().store(MemFlags::new(), t, trampoline, 0);
                    }
                    Lir::CloseOver(x) => {
                        let proto = proto.constants[*x as usize].get_raw();
                        let x = self.builder.ins().iconst(types::I64, proto as i64);
                        self.push(x);
                        self.update_frame();
                        self.builder
                            .ins()
                            .call(self.close_over, &[thread, self.frame]);
                        self.load_frame();
                    }
                    Lir::Constant(x) => {
                        let constant = proto.constants[*x as usize].get_raw();
                        let x = self.builder.ins().iconst(types::I64, constant as i64);
                        self.push(x);
                    }
                    Lir::Int32(x) => {
                        let x = self.builder.ins().iconst(
                            types::I64,
                            crate::runtime::value::Value::new(*x).get_raw() as i64,
                        );
                        self.push(x);
                    }
                    Lir::N => {
                        let x = self.builder.ins().iconst(
                            types::I64,
                            crate::runtime::value::Value::new(Null).get_raw() as i64,
                        );
                        self.push(x);
                    }
                    Lir::F => {
                        let x = self.builder.ins().iconst(
                            types::I64,
                            crate::runtime::value::Value::new(false).get_raw() as i64,
                        );
                        self.push(x);
                    }

                    Lir::T => {
                        let x = self.builder.ins().iconst(
                            types::I64,
                            crate::runtime::value::Value::new(true).get_raw() as i64,
                        );
                        self.push(x);
                    }

                    Lir::GlobalGet(x) => {
                        let sym = proto.constants[*x as usize].downcast::<ScmSymbol>();
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
                    Lir::GlobalSet(x) => {
                        let sym = proto.constants[*x as usize].downcast::<ScmSymbol>();
                        let sym = self
                            .builder
                            .ins()
                            .iconst(types::I64, unsafe { std::mem::transmute::<_, i64>(sym) });
                        let off = gc_offsetof!(ScmSymbol, value);
                        let val = self.pop();
                        self.builder
                            .ins()
                            .store(MemFlags::new(), val, sym, off as i32);
                    }
                    Lir::UpvalueGet(x) => {
                        let at = *x;
                        let upvalues_offset = gc_offsetof!(Closure, upvalues);
                        let upvalues = self.builder.ins().load(
                            types::I64,
                            MemFlags::new(),
                            closure,
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
                    Lir::UpvalueSet(x) => {
                        let at = *x;
                        let value = self.pop();
                        let upvalues_offset = gc_offsetof!(Closure, upvalues);
                        let upvalues = self.builder.ins().load(
                            types::I64,
                            MemFlags::new(),
                            closure,
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
                    Lir::Apply(x) => {
                        let func = self.pop();
                        self.update_frame();
                        let nargs = self.builder.ins().iconst(types::I32, *x as i64);
                        let call = self.builder.ins().call(
                            self.jit_apply,
                            &[thread, self.frame, func, nargs, trampoline],
                        );
                        self.load_frame();

                        let value = self.builder.inst_results(call)[0];
                        let result =
                            self.builder
                                .ins()
                                .load(types::I8, MemFlags::new(), trampoline, 0);
                        let exc = self
                            .builder
                            .ins()
                            .iconst(types::I8, Trampoline::Exception as i64);
                        let then = self.builder.create_block();
                        self.builder.ins().br_icmp(
                            IntCC::Equal,
                            result,
                            exc,
                            return_block,
                            &[value],
                        );
                        self.builder.ins().jump(then, &[]);
                        self.builder.switch_to_block(then);
                        self.push(value);
                    }
                    Lir::IBin(op) => {
                        let x = self.pop();
                        let y = self.pop();
                        let xi = self.get_int32(x);
                        let yi = self.get_int32(y);
                        let z = match op {
                            Bin::Add => {
                                let val = self.builder.ins().iadd(xi, yi);
                                self.box_wtag(val, INT32_TAG)
                            }
                            _ => todo!(),
                        };
                        self.push(z);
                    }
                    _ => (),
                }
            }
        }
        self.builder.switch_to_block(return_block);
        let val = self.builder.block_params(return_block)[0];
        self.builder.ins().return_(&[val]);
    }

    pub fn update_frame(&mut self) {
        let si = self.builder.use_var(self.si);
        self.builder.ins().store(
            MemFlags::new(),
            si,
            self.frame,
            offset_of!(CallFrame, si) as i32,
        );
    }
    pub fn get_int32(&mut self, val: ir::Value) -> ir::Value {
        self.builder.ins().ireduce(types::I32, val)
    }

    pub fn box_wtag(&mut self, val: ir::Value, tag: u32) -> ir::Value {
        let tag = (tag as u64) << Value::NUM_DATA_BITS as u64;
        let val = self.builder.ins().uextend(types::I64, val);
        self.builder.ins().bor_imm(val, tag as i64)
    }
    pub fn value_tag(&mut self, val: ir::Value) -> ir::Value {
        self.builder
            .ins()
            .ushr_imm(val, Value::NUM_DATA_BITS as i64)
    }
    pub fn is_pointer(&mut self, val: ir::Value) -> ir::Value {
        let tag = self.value_tag(val);
        self.builder
            .ins()
            .icmp_imm(IntCC::Equal, tag, OBJECT_TAG as i64)
    }

    pub fn is_int(&mut self, val: ir::Value) -> ir::Value {
        let tag = self.value_tag(val);
        self.builder
            .ins()
            .icmp_imm(IntCC::Equal, tag, INT32_TAG as i64)
    }
    pub fn load_frame(&mut self) {
        let si = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            self.frame,
            offset_of!(CallFrame, si) as i32,
        );
        self.builder.def_var(self.si, si);
    }

    pub fn is_false_or_null(&mut self, val: ir::Value) -> ir::Value {
        let null = self
            .builder
            .ins()
            .iconst(types::I64, Value::new(Null).get_raw() as i64);
        let false_ = self
            .builder
            .ins()
            .iconst(types::I64, Value::new(false).get_raw() as i64);
        let is_null = self.builder.ins().icmp(IntCC::Equal, val, null);
        let is_false = self.builder.ins().icmp(IntCC::Equal, val, false_);
        self.builder.ins().bor(is_null, is_false)
    }

    pub fn pop_or_undef(&mut self) -> ir::Value {
        let mut si = self.builder.use_var(self.si);
        let osi = si;
        let if_zero = self.builder.create_block();
        let if_nzero = self.builder.create_block();
        let merge = self.builder.create_block();
        self.builder.append_block_param(merge, types::I64);
        self.builder.append_block_param(merge, types::I64);
        self.builder.ins().brz(si, if_zero, &[]);
        self.builder.ins().jump(if_nzero, &[]);
        self.builder.switch_to_block(if_nzero);
        let y = self.builder.ins().iconst(types::I64, 1);
        si = self.builder.ins().isub(si, y);
        let six = self.builder.ins().imul_imm(si, 8);
        let bp = self.builder.ins().iadd(self.bp, six);
        let value = self.builder.ins().load(types::I64, MemFlags::new(), bp, 0);
        self.builder.ins().jump(merge, &[value, si]);

        self.builder.switch_to_block(if_zero);
        let val = self
            .builder
            .ins()
            .iconst(types::I64, Value::new(Undefined).get_raw() as i64);
        self.builder.ins().jump(merge, &[val, osi]);
        self.builder.switch_to_block(merge);
        let si = self.builder.block_params(merge)[1];
        let val = self.builder.block_params(merge)[0];
        self.builder.def_var(self.si, si);
        val
    }
    pub fn top(&mut self) -> ir::Value {
        let mut si = self.builder.use_var(self.si);
        let y = self.builder.ins().iconst(types::I64, 1);
        si = self.builder.ins().isub(si, y);
        let six = self.builder.ins().imul_imm(si, 8);
        let ptr = self.builder.ins().iadd(self.bp, six);
        self.builder.ins().load(types::I64, MemFlags::new(), ptr, 0)
    }
    pub fn stack_at(&mut self, x: i32) -> ir::Value {
        let mut si = self.builder.use_var(self.si);

        si = self.builder.ins().iadd_imm(si, x as i64);
        let six = self.builder.ins().imul_imm(si, 8);
        let ptr = self.builder.ins().iadd(self.bp, six);
        self.builder.ins().load(types::I64, MemFlags::new(), ptr, 0)
    }
    pub fn pop(&mut self) -> ir::Value {
        let mut si = self.builder.use_var(self.si);
        let y = self.builder.ins().iconst(types::I64, 1);
        si = self.builder.ins().isub(si, y);
        let six = self.builder.ins().imul_imm(si, 8);
        self.builder.def_var(self.si, si);
        let bp = self.bp;
        let ptr = self.builder.ins().iadd(bp, six);
        let value = self.builder.ins().load(types::I64, MemFlags::new(), ptr, 0);
        value
    }

    pub fn push(&mut self, value: ir::Value) {
        let mut si = self.builder.use_var(self.si);
        let six = self.builder.ins().imul_imm(si, 8);
        let ptr = self.builder.ins().iadd(self.bp, six);
        self.builder.ins().store(MemFlags::new(), value, ptr, 0);
        si = self.builder.ins().iadd_imm(si, 1);
        self.builder.def_var(self.si, si);
    }

    pub fn env_ptr(&mut self, at: u16) -> ir::Value {
        self.builder.ins().iadd_imm(self.env, at as i64 * 8)
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
        self.builder.ins().band_imm(val, Value::DATA_MASK as i64)
    }
}
