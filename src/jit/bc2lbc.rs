use super::lbc::{Access, LBCBlock, LBCFunction, LBC};
use crate::{compiler::Op, runtime::value::ScmPrototype, Managed};
use std::collections::{BTreeMap, VecDeque};

#[allow(dead_code)]
pub struct BC2LBC<'a> {
    func: LBCFunction,
    code: &'a [Op],

    to_be_generated: VecDeque<ToBeGenerated>,
    blocks: BTreeMap<u32, LBCBlock>,

    instr_index: usize,
    end_of_basic_block: bool,
    fallthrough: bool,
    runoff: usize,
    current: LBCBlock,
    osr: Vec<(u32, LBCBlock)>,
    proto: Managed<ScmPrototype>,
}

#[allow(dead_code)]
struct ToBeGenerated {
    block: LBCBlock,
    low: u32,
    high: u32,
    max: u32,
}

impl<'a> BC2LBC<'a> {
    pub fn new(proto: Managed<ScmPrototype>, code: &'a [Op]) -> Self {
        Self {
            proto,
            code,
            blocks: Default::default(),
            to_be_generated: VecDeque::new(),
            instr_index: 0,
            end_of_basic_block: false,
            fallthrough: false,
            osr: vec![],
            func: LBCFunction::new(),
            runoff: 0,
            current: LBCBlock(0),
        }
    }

    pub fn get_or_create_block(&mut self, target: u32) -> LBCBlock {
        self.end_of_basic_block = true;
        *self.blocks.entry(target).or_insert_with(|| {
            let block = self.func.new_block();
            let gen = ToBeGenerated {
                low: target as _,
                max: u32::MAX,
                high: target as _,
                block,
            };
            self.to_be_generated.push_back(gen);
            block
        })
    }

    pub fn generate(mut self) -> LBCFunction {
        self.func.stack_max = self.proto.stack_max as _;
        self.func.argc = self.proto.arguments as _;
        let block = self.func.new_block();
        self.func.blocks[block.0 as usize].entrypoint = Some(0);
        self.current = block;
        self.generate_from(0);

        while let Some(to_generate) = self.to_be_generated.pop_front() {
            let at = to_generate.low as usize;
            let block = to_generate.block;
            self.current = block;
            self.func.switch_to_block(block);
            self.generate_from(at);
        }

        while let Some((target, block)) = self.osr.pop() {
            self.func.switch_to_block(block);
            let osr_target = self.get_or_create_block(target);
            self.func.emit(LBC::OSR(osr_target));
            self.func.entrypoints.push(block);
        }

        self.func
    }

    pub fn generate_from(&mut self, from: usize) {
        self.func.switch_to_block(self.current);
        let mut index = from;
        self.end_of_basic_block = false;
        self.fallthrough = false;
        loop {
            self.instr_index = index;
            let code = &self.code[index..];
            match code {
                [Op::LoopHint, Op::Jump(target), ..] => {
                    let block = self.get_or_create_block(*target);
                    let osr_entrypoint = self.func.new_block();
                    self.osr.push((*target, osr_entrypoint));
                    self.func.blocks[osr_entrypoint.0 as usize].entrypoint = Some(index as u32);
                    self.proto.entry_points.insert(index as _, osr_entrypoint.0);
                    self.func.emit(LBC::Jump(block));
                    self.end_of_basic_block = true;
                    index += 2;
                }
                [Op::PushFalse, Op::JumpIfFalse(x), ..]
                | [Op::PushNull, Op::JumpIfFalse(x), ..] => {
                    let target_block = self.get_or_create_block(*x);
                    self.func.emit(LBC::Jump(target_block));
                    self.end_of_basic_block = true;
                    index += 2;
                }
                [Op::PushConstant(x), Op::GlobalGet, ..] => {
                    index += 2;
                    self.func.emit(LBC::Get(Access::Global(*x)));
                }

                [Op::Jump(target), ..] => {
                    let target = self.get_or_create_block(*target);
                    self.func.emit(LBC::Jump(target));
                    self.end_of_basic_block = true;
                    index += 1;
                }
                [Op::JumpIfFalse(target), ..] => {
                    let target = self.get_or_create_block(*target);
                    self.func.emit(LBC::JumpIfFalse(target));

                    self.end_of_basic_block = true;
                    self.fallthrough = true;
                    index += 1;
                }

                [Op::LocalGet(local), ..] => {
                    self.func.emit(LBC::Get(Access::Local(*local)));
                    index += 1;
                }

                [Op::LocalSet(local), ..] => {
                    self.func.emit(LBC::Set(Access::Local(*local)));
                    index += 1;
                }

                [Op::UpvalueGet(upval), ..] => {
                    self.func.emit(LBC::Get(Access::Upvalue(*upval)));
                    index += 1;
                }
                [Op::UpvalueSet(upval), ..] => {
                    self.func.emit(LBC::Set(Access::Upvalue(*upval)));
                    index += 1;
                }
                [Op::PushConstant(c), Op::CloseOver, ..] => {
                    self.func.emit(LBC::Closure(*c));
                    index += 1;
                }
                [Op::Apply(nargs), ..] => {
                    self.func.emit(LBC::Call(*nargs));
                    index += 1;
                }
                [Op::TailApply(nargs), ..] => {
                    self.func.emit(LBC::Trampoline(*nargs));
                    self.func.emit(LBC::ReturnUndef);
                    self.end_of_basic_block = true;
                    index += 1;
                }
                [Op::PushInt(x), ..] => {
                    self.func.emit(LBC::Imm32(*x));
                    index += 1;
                }
                [Op::Return, ..] => {
                    self.func.emit(LBC::Return);
                    index += 1;
                    self.end_of_basic_block = true;
                }
                [Op::PushNull, ..] => {
                    index += 1;
                    self.func.emit(LBC::ImmNull);
                }
                [Op::Pop, ..] => {
                    self.func.emit(LBC::Pop);
                    index += 1;
                }

                _ => todo!("{:?}", code),
            }

            if !self.end_of_basic_block && index == self.runoff {
                self.end_of_basic_block = true;
                self.fallthrough = true;
            }
            if self.end_of_basic_block {
                if self.fallthrough {
                    let block = self.get_or_create_block(index as _);
                    self.func.emit(LBC::Jump(block));
                }
                return;
            }
        }
    }
}
