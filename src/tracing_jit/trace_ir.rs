use crate::runtime::value::Value;

pub enum Trace {
    PushConstant(u32),
    PushInt(i32),
    PushT,
    PushF,
    PushN,
    /// Call to immutable native function. For most native procedures inline code is generated instead
    CallConst(u32, u16),
    /// When tracing JIT sees tail call to native function it just setups trampoline for it
    Trampoline(u16),
    /// Call to not inline-able native function
    Call(u16),
    /// No other guards lol
    GuardTrue(u32 /* Index of opcode to return to if guard fails */),
    GuardFalse(u32),
    EnterFrame(Value),
    LeaveFrame,
    LeaveFrameUndef,

    IsInt,
    IsFloat,
    IsString,
    IsCons,
    IsCell(u32),
    IsBool,
    IsNull,
    IsUndef,
    IsList,
    IsVector,
    IsBlob,

    IBin(Binary),
    FBin(Binary),
    CloseOver(u32),

    LinkLoop,
    LinkReturn,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Binary {
    Add,
    Sub,
    Div,
    Mul,
    Gt,
    Lt,
    Ge,
    Le,
    Eq,
}
