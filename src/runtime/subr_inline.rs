use crate::jit::{
    bc2lbc::BC2LBC,
    lbc::{Access, LBCBlock, Type, LBC},
};

pub fn car_inline(
    cc: &mut BC2LBC,
    slow: &mut dyn FnMut(&mut BC2LBC) -> LBCBlock,
    argc: u16,
) -> bool {
    if argc != 1 {
        return false;
    }
    let slowpath = slow(cc);
    let then = cc.func.new_block();
    cc.func.emit(LBC::JumpIfNotType(Type::Cons, slowpath));
    cc.func.emit(LBC::Jump(then));
    cc.func.switch_to_block(then);
    cc.func.emit(LBC::Get(Access::Car));

    true
}

pub fn cdr_inline(
    cc: &mut BC2LBC,
    slow: &mut dyn FnMut(&mut BC2LBC) -> LBCBlock,
    argc: u16,
) -> bool {
    if argc != 1 {
        return false;
    }
    let slowpath = slow(cc);
    let then = cc.func.new_block();
    cc.func.emit(LBC::JumpIfNotType(Type::Cons, slowpath));
    cc.func.emit(LBC::Jump(then));
    cc.func.switch_to_block(then);
    cc.func.emit(LBC::Get(Access::Cdr));

    true
}

pub fn list_inline(
    cc: &mut BC2LBC,
    _slow: &mut dyn FnMut(&mut BC2LBC) -> LBCBlock,
    argc: u16,
) -> bool {
    if argc == 0 {
        cc.func.emit(LBC::ImmNull)
    } else {
        cc.func.emit(LBC::List(argc))
    }
    true
}

pub fn nullp_inline(
    cc: &mut BC2LBC,
    _slow: &mut dyn FnMut(&mut BC2LBC) -> LBCBlock,
    argc: u16,
) -> bool {
    if argc == 1 {
        cc.func.emit(LBC::Is(Type::Null));
        true
    } else {
        false
    }
}

pub fn cons_inline(
    cc: &mut BC2LBC,
    _slow: &mut dyn FnMut(&mut BC2LBC) -> LBCBlock,
    argc: u16,
) -> bool {
    if argc == 2 {
        cc.func.emit(LBC::Cons);
        true
    } else {
        false
    }
}
