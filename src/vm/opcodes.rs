#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Opcode {
    /// R(A) = R(B)  
    Move(u8, u8),
    /// R(A) = i32(B)
    LoadI(u8, i32),
    /// R(A) = null
    LoadN(u8),
    /// R(A) = #t
    LoadF(u8),
    /// R(B) = #f
    LoadT(u8),
    /// R(A) = CONSTANTS(B)
    LoadK(u8, u16),
    /// R(A) = CLOSURE.UPVALUES[B]
    LoadU(u8, u8),
    /// R(A) = CONSTANTS[B].SYM.VALUE
    LoadG(u8, u16),
    /// CONSTANTS[A].SYM.VALUE = R(B)
    StoreG(u16, u8),

    /// R(A) = CLOSURE(R(B))
    Closure(u8, u8),
    /// CLOSURE.UPVALUES[A] = R(B)
    StoreU(u8, u8),
    /// R(A) = apply(R(B), R(B+1)..R(B+C))
    Apply(u8, u8, u8),
    // tail-apply(R(B), R(B+1)..R(B+C))
    TailApply(u8, u8),
    /// ip = B
    Jump(u32),
    /// if R(A) == #f: ip = B
    JumpIfFalse(u8, u32),
    /// if R(A) != #f: ip = B
    JumpIfTrue(u8, u32),
    /// return R(A)
    Return(u8),
    Return0,
}
