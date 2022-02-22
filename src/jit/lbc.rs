//! # LBC - low level bytecode
//!
//! LBC is also a stack based bytecode but with support for a lot of scheme primitives in it. This helps us to output optimized machine code from Scheme bytecode.

use comet::{api::Collectable, ConstantId};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LBC {
    Imm32(i32),
    Constant(u32),
    ImmFalse,
    ImmTrue,
    ImmNull,
    ImmUndef,

    Get(Access),
    Set(Access),
    Math(Math),
    Not,

    Closure(u32),

    Return,
    ReturnUndef,

    Dup,
    Swap,

    CallStatic(u32, u16),
    Call(u16),
    Trampoline(u16),
    TrampolineStatic(u32, u16),
    SelfTailCall,

    JumpIfFalse(LBCBlock),
    JumpIfTrue(LBCBlock),
    JumpIfType(Type, LBCBlock),
    JumpIfNotType(Type, LBCBlock),

    JumpIfType2(Type, LBCBlock),
    JumpIfNotType2(Type, LBCBlock),
    JumpIfType2x2(Type, Type, LBCBlock),
    JumpIfNotType2x2(Type, Type, LBCBlock),
    Jump(LBCBlock),
    OSR(LBCBlock),
    Pop,
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Access {
    Upvalue(u16),
    Local(u16),
    Stack(i16),
    Global(u32),
    Vector,
    Car,
    Cdr,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Math {
    Int32Binary(Binary),
    DoubleBinary(Binary),

    Floor,
    Round,
    Truncate,
    Ceiling,

    Sin,
    Cos,
    Tan,
    Atan,
    Asin,
    Acos,
    Sinh,
    Cosh,
    Tanh,

    BitwiseIOr,
    BitwiseAnd,
    BitwiseXor,
    BitwiseNot,

    BitwiseBitSetP,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Binary {
    Add,
    Sub,
    Div,
    Mul,
    Rem,

    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    Equal,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Type {
    Dynamic,
    Int32,
    Double,
    Bool,
    Null,
    Undefined,

    Heap(u32),
}

impl Type {
    pub fn heap<T: Collectable>() -> Self {
        Self::Heap(ConstantId::<T>::ID)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LBCBlock(pub u32);

impl std::fmt::Debug for LBCBlock {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(fmt, "block.{}", self.0)
    }
}

impl std::fmt::Display for LBCBlock {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(fmt, "block.{}", self.0)
    }
}

pub struct BasicBlock {
    /// true if this basic block is entrypoint i.e start of loop or first block in the function
    pub entrypoint: Option<u32>,
    pub code: Vec<LBC>,
    pub id: LBCBlock,
}

pub struct LBCFunction {
    pub blocks: Vec<BasicBlock>,
    pub stack_max: u16,
    pub argc: u16,
    pub entrypoints: Vec<LBCBlock>,
    pub current: Option<LBCBlock>,
}

impl LBCFunction {
    pub fn new() -> Self {
        Self {
            blocks: vec![],
            stack_max: 0,
            argc: 0,
            current: None,
            entrypoints: Vec::new(),
        }
    }
    pub fn new_block(&mut self) -> LBCBlock {
        let id = self.blocks.len();
        self.blocks.push(BasicBlock {
            entrypoint: None,
            code: vec![],
            id: LBCBlock(id as _),
        });
        LBCBlock(id as _)
    }

    pub fn is_filled(&self) -> bool {
        self.current.is_none() || {
            let block = &self.blocks[self.current.unwrap().0 as usize];
            let last = block.code.last();
            match last {
                Some(lir) => match lir {
                    LBC::Jump(_) | LBC::Return | LBC::ReturnUndef => true,
                    _ => false,
                },
                _ => false,
            }
        }
    }
    pub fn switch_to_block(&mut self, block: LBCBlock) {
        self.current = Some(block);
    }

    pub fn emit(&mut self, ins: LBC) {
        let id = self.current.expect("no basic block present");
        self.blocks[id.0 as usize].code.push(ins);
    }

    pub fn display(&self) -> LBCDisplay<'_> {
        LBCDisplay { func: self }
    }
}

pub struct LBCDisplay<'a> {
    func: &'a LBCFunction,
}

impl<'a> std::fmt::Display for LBCDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "function ({}) {{", self.func.argc)?;
        writeln!(f, "stack_size: {}", self.func.stack_max)?;
        for block in self.func.blocks.iter() {
            writeln!(f, "{}: ", block.id)?;
            for op in block.code.iter() {
                write!(f, "    ")?;
                match op {
                    LBC::Pop => writeln!(f, "pop")?,
                    LBC::Imm32(x) => writeln!(f, "int32 {}", x)?,
                    LBC::ImmNull => writeln!(f, "null")?,
                    LBC::ImmFalse | LBC::ImmTrue => writeln!(f, "{}", *op == LBC::ImmTrue)?,
                    LBC::Constant(x) => writeln!(f, "get.const %{}", x)?,
                    LBC::Call(x) => writeln!(f, "call_dynamic {}", x)?,
                    LBC::CallStatic(x, y) => writeln!(f, "call_static %{}, {}", x, y)?,
                    LBC::Trampoline(x) => writeln!(f, "trampoline_dynamic {}", x)?,
                    LBC::TrampolineStatic(x, y) => writeln!(f, "trampoline_static {}, {}", x, y)?,
                    LBC::Jump(x) => writeln!(f, "jump {}", x)?,
                    LBC::JumpIfFalse(x) => writeln!(f, "brfalse {}", x)?,
                    LBC::JumpIfTrue(x) => writeln!(f, "brtrue {}", x)?,
                    LBC::JumpIfType(x, target) => writeln!(f, "brtype {:?}, {}", x, target)?,
                    LBC::JumpIfType2(x, target) => writeln!(f, "brtype_2 {:?}, {}", x, target)?,
                    LBC::JumpIfType2x2(x, y, target) => {
                        writeln!(f, "brtype {:?}. {:?}, {} ", x, y, target)?
                    }
                    LBC::JumpIfNotType(x, target) => writeln!(f, "brntype {:?}, {}", x, target)?,
                    LBC::JumpIfNotType2(x, target) => writeln!(f, "brntype_2 {:?}, {}", x, target)?,
                    LBC::JumpIfNotType2x2(x, y, target) => {
                        writeln!(f, "brntype {:?}. {:?}, {} ", x, y, target)?
                    }
                    LBC::ImmUndef => writeln!(f, "undef")?,
                    LBC::Get(acc) => {
                        write!(f, "get.")?;
                        match acc {
                            Access::Global(x) => writeln!(f, "global %{}", x)?,
                            Access::Car => writeln!(f, "car")?,
                            Access::Cdr => writeln!(f, "cdr")?,
                            Access::Stack(at) => writeln!(f, "stack {}", at)?,
                            Access::Local(at) => writeln!(f, "local %{}", at)?,
                            Access::Upvalue(at) => writeln!(f, "upvalue %{}", at)?,
                            Access::Vector => writeln!(f, "vector")?,
                        }
                    }

                    LBC::Set(acc) => {
                        write!(f, "set.")?;
                        match acc {
                            Access::Global(x) => writeln!(f, "global %{}", x)?,
                            Access::Car => writeln!(f, "car")?,
                            Access::Cdr => writeln!(f, "cdr")?,
                            Access::Stack(at) => writeln!(f, "stack {}", at)?,
                            Access::Local(at) => writeln!(f, "local %{}", at)?,
                            Access::Upvalue(at) => writeln!(f, "upvalue %{}", at)?,
                            Access::Vector => writeln!(f, "vector")?,
                        }
                    }
                    LBC::Not => writeln!(f, "not")?,
                    LBC::Closure(x) => writeln!(f, "make_closure %{}", x)?,
                    LBC::Math(m) => match m {
                        Math::Int32Binary(b) | Math::DoubleBinary(b) => {
                            if let Math::Int32Binary(_) = m {
                                write!(f, "i")?;
                            } else {
                                write!(f, "f")?;
                            }
                            match b {
                                Binary::Add => writeln!(f, "add")?,
                                Binary::Sub => writeln!(f, "sub")?,
                                Binary::Div => writeln!(f, "div")?,
                                Binary::Mul => writeln!(f, "mul")?,
                                Binary::Rem => writeln!(f, "rem")?,
                                Binary::GreaterThan => writeln!(f, "gt")?,
                                Binary::GreaterThanOrEqual => writeln!(f, "gte")?,
                                Binary::LessThan => writeln!(f, "lt")?,
                                Binary::LessThanOrEqual => writeln!(f, "lte")?,
                                Binary::Equal => writeln!(f, "eq")?,
                            }
                        }
                        x => {
                            let x = format!("{:?}", x).to_lowercase();
                            writeln!(f, "{}", x)?
                        }
                    },
                    LBC::Return => writeln!(f, "return")?,
                    LBC::ReturnUndef => writeln!(f, "return undef")?,
                    LBC::Dup => writeln!(f, "dup")?,
                    LBC::Swap => writeln!(f, "swap")?,
                    LBC::SelfTailCall => writeln!(f, "self_tail_call")?,
                    LBC::OSR(to) => writeln!(f, "osr {}", to)?,
                }
            }
        }
        writeln!(f, "}}")?;

        Ok(())
    }
}
