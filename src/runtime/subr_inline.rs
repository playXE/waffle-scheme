use comet::ConstantId;

use crate::method_jit::lir::*;
use crate::method_jit::lower::FunctionLowerer;

use super::value::ScmCons;
pub fn car_inline(
    gen: &mut FunctionLowerer,
    slowpath: &mut dyn FnMut(&mut FunctionLowerer) -> u32,
    argc: u16,
) -> bool {
    if argc != 1 {
        return false;
    }

    let slowpath = slowpath(gen);
    gen.gen
        .emit(Lir::JumpNotCellOf(ConstantId::<ScmCons>::ID, slowpath));
    let next_block = gen.gen.new_block();
    gen.gen.emit(Lir::Jump(next_block));
    gen.gen.switch_to_block(next_block);
    gen.gen.emit(Lir::Car);

    true
}
