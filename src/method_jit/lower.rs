use super::lir::LIRGen;
use super::lir::*;
use crate::compiler::Op;
use crate::runtime::value::NativeFunction;
use crate::runtime::value::ScmPrototype;
use crate::runtime::value::ScmSymbol;
use crate::runtime::SchemeThread;
use crate::Managed;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::mem::size_of;

fn label_targets(code: &[Op]) -> BTreeMap<u32, bool> {
    let mut targets = BTreeMap::new();
    for ins in code {
        match ins {
            Op::Jump(t) => {
                targets.insert(*t, false);
            }
            Op::JumpIfFalse(t) => {
                targets.insert(*t, true);
            }
            _ => (),
        }
    }
    targets
}

pub struct FunctionLowerer<'a> {
    pub gen: LIRGen,
    targets: BTreeMap<u32, bool>,
    code: &'a [Op],
    label_to_block: HashMap<u32, u32>,
}

impl<'a> FunctionLowerer<'a> {
    pub fn new(code: &'a [Op]) -> Self {
        let targets = label_targets(code);
        Self {
            gen: LIRGen::new(),
            targets,
            code,
            label_to_block: HashMap::new(),
        }
    }

    pub fn get_or_create_block(&mut self, label: u32) -> u32 {
        *self
            .label_to_block
            .entry(label)
            .or_insert_with(|| self.gen.new_block())
    }

    pub fn lower(&mut self, thread: &mut SchemeThread, mut proto: Managed<ScmPrototype>) {
        let mut i = 0;
        let entry = self.gen.new_block();
        self.gen.blocks[entry as usize].entrypoint = Some(0);
        proto.entry_points.insert(&mut thread.mutator, 0, 0);
        self.gen.switch_to_block(entry);
        while i < self.code.len() {
            if let Some(_cond) = self.targets.get(&(i as u32)).copied() {
                let block = self.get_or_create_block(i as _);

                if !self.gen.is_filled() {
                    self.gen.emit(Lir::Jump(block));
                }
                self.gen.switch_to_block(block);
            }

            match &self.code[i..] {
                [Op::LoopHint, Op::Jump(target), ..] => {
                    let entry_point = self.gen.new_block();
                    self.gen.emit(Lir::Jump(entry_point));

                    proto
                        .entry_points
                        .insert(&mut thread.mutator, i as u32, entry_point);
                    self.gen.blocks[entry_point as usize].entrypoint = Some(i as u32);
                    self.gen.switch_to_block(entry_point);

                    let target = self.get_or_create_block(*target);
                    self.gen.emit(Lir::Jump(target));
                    i += 2;
                }
                [Op::PushConstant(x), Op::GlobalGet, Op::Apply(nargs), ..] => {
                    let sym = proto.constants[*x as usize].downcast::<ScmSymbol>();
                    if !sym.mutable && sym.value.native_functionp() {
                        let func = sym.value.downcast::<NativeFunction>();
                        if let Some(transformer) = func.transformer {
                            let mut slowpath = None;
                            let mut cb = |gen: &mut FunctionLowerer| {
                                if let Some(block) = slowpath {
                                    return block;
                                }
                                slowpath = Some(gen.gen.new_block());

                                slowpath.unwrap()
                            };
                            if transformer(self, &mut cb, *nargs) {
                                if let Some(block) = slowpath {
                                    let merge_block = self.gen.new_block();
                                    self.gen.emit(Lir::Jump(merge_block));
                                    self.gen.switch_to_block(block);
                                    self.gen.emit(Lir::GlobalGet(*x));
                                    self.gen.emit(Lir::Apply(*nargs));
                                    self.gen.emit(Lir::Jump(merge_block));
                                    self.gen.switch_to_block(merge_block);
                                }
                                i += 3;
                                continue;
                            }
                        }
                    }
                    self.gen.emit(Lir::GlobalGet(*x));
                    self.gen.emit(Lir::Apply(*nargs));
                    i += 3;
                }

                [Op::PushConstant(x), Op::GlobalGet, Op::TailApply(nargs), ..] => {
                    let sym = proto.constants[*x as usize].downcast::<ScmSymbol>();
                    if !sym.mutable && sym.value.native_functionp() {
                        let func = sym.value.downcast::<NativeFunction>();
                        if let Some(transformer) = func.transformer {
                            let mut slowpath = None;
                            let mut cb = |gen: &mut FunctionLowerer| {
                                if let Some(block) = slowpath {
                                    return block;
                                }
                                slowpath = Some(gen.gen.new_block());

                                slowpath.unwrap()
                            };
                            if transformer(self, &mut cb, *nargs) {
                                self.gen.emit(Lir::Ret);
                                if let Some(block) = slowpath {
                                    self.gen.switch_to_block(block);
                                    self.gen.emit(Lir::GlobalGet(*x));
                                    self.gen.emit(Lir::Trampoline(*nargs));
                                    self.gen.emit(Lir::RetUndef);
                                }
                                let next_block = self.gen.new_block();
                                self.gen.switch_to_block(next_block);
                                i += 3;
                                continue;
                            }
                        }
                    }
                    self.gen.emit(Lir::GlobalGet(*x));
                    self.gen.emit(Lir::Trampoline(*nargs));
                    self.gen.emit(Lir::RetUndef);
                    let next_block = self.gen.new_block();
                    self.gen.switch_to_block(next_block);
                    i += 3;
                }
                [Op::PushFalse, Op::JumpIfFalse(x), ..]
                | [Op::PushNull, Op::JumpIfFalse(x), ..] => {
                    let target_block = self.get_or_create_block(*x);
                    self.gen.emit(Lir::Jump(target_block));

                    i = *x as usize;
                }
                [Op::PushConstant(_), Op::JumpIfFalse(_), ..]
                | [Op::PushInt(_), Op::JumpIfFalse(_), ..]
                | [Op::PushTrue, Op::JumpIfFalse(_), ..] => {
                    // skip jump if possible
                    i += 2;
                }

                [Op::Jump(x), ..] => {
                    let target = self.get_or_create_block(*x);
                    self.gen.emit(Lir::Jump(target));
                    i += 1;
                }
                [Op::JumpIfFalse(x), ..] => {
                    let next_block = self.get_or_create_block(i as u32 + 1);
                    let target_block = self.get_or_create_block(*x);

                    self.gen.emit(Lir::JumpIfFalse(target_block));
                    self.gen.emit(Lir::Jump(next_block));
                    self.gen.switch_to_block(next_block);
                    i += 1;
                }
                [Op::LocalGet(x), ..] => {
                    self.gen.emit(Lir::LocalGet(*x));
                    i += 1;
                }
                [Op::LocalSet(x), ..] => {
                    self.gen.emit(Lir::LocalSet(*x));
                    i += 1;
                }
                [Op::UpvalueGet(x), ..] => {
                    self.gen.emit(Lir::UpvalueGet(*x));
                    i += 1;
                }
                [Op::UpvalueSet(x), ..] => {
                    self.gen.emit(Lir::UpvalueSet(*x));
                    i += 1;
                }
                [Op::PushConstant(x), Op::GlobalGet, ..] => {
                    self.gen.emit(Lir::GlobalGet(*x));
                    i += 2;
                }
                [Op::PushConstant(x), Op::GlobalSet, ..] => {
                    self.gen.emit(Lir::GlobalSet(*x));
                    i += 2;
                }
                [Op::Apply(nargs), ..] => {
                    self.gen.emit(Lir::Apply(*nargs));
                    i += 1;
                }
                [Op::TailApply(nargs), ..] => {
                    self.gen.emit(Lir::Trampoline(*nargs));
                    self.gen.emit(Lir::RetUndef);
                    let next_block = self.gen.new_block();
                    self.gen.switch_to_block(next_block);
                    i += 1;
                }
                [Op::Return, ..] => {
                    self.gen.emit(Lir::Ret);
                    i += 1;
                }
                [Op::PushConstant(x), Op::CloseOver, ..] => {
                    self.gen.emit(Lir::CloseOver(*x));
                    i += 2;
                }
                [Op::PushInt(x), ..] => {
                    self.gen.emit(Lir::Int32(*x));
                    i += 1;
                }
                [Op::PushConstant(x), ..] => {
                    self.gen.emit(Lir::Constant(*x));
                    i += 1;
                }
                [Op::Pop, ..] => {
                    i += 1;
                    self.gen.emit(Lir::Pop);
                }
                [Op::PushNull, ..] => {
                    i += 1;
                    self.gen.emit(Lir::N);
                }
                [x, ..] => todo!("{:?}", x),
                x => todo!("{:?}", x),
            }
        }
    }
}

pub fn lower(thread: &mut SchemeThread, proto: Managed<ScmPrototype>) -> LIRGen {
    let code = proto.code.as_ptr();
    let code = unsafe {
        std::slice::from_raw_parts(code.cast::<Op>(), proto.code.len() / size_of::<Op>())
    };
    let mut lowerer = FunctionLowerer::new(code);
    lowerer.lower(thread, proto);

    lowerer.gen
}
