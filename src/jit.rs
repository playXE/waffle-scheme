use std::mem::size_of;

use cranelift::{
    frontend::FunctionBuilder,
    prelude::{types, InstBuilder, MemFlags, StackSlotData},
};
use cranelift_jit::JITModule;
use memoffset::offset_of;

use crate::{
    runtime::{
        value::{ScmPrototype, Value},
        vm::Frame,
        SchemeThread,
    },
    Managed,
};
use cranelift::prelude::codegen::ir;
pub struct FunctionTranslator<'a> {
    builder: FunctionBuilder<'a>,
    module: &'a mut JITModule,
}

impl<'a> FunctionTranslator<'a> {
    fn translate(&mut self, func: Managed<ScmPrototype>, thread: ir::Value, closure: ir::Value) {
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

        let frame_slot = self.builder.create_stack_slot(StackSlotData {
            kind: cranelift::prelude::StackSlotKind::ExplicitSlot,
            size: size_of::<Frame>() as _,
        });

        let stack = self.builder.ins().stack_addr(types::I64, stack_slot, 0);
        let locals = self
            .builder
            .ins()
            .stack_addr(types::I64, stack_slot, func.stack_max as i32);
        let upvalues = self.builder.ins().stack_addr(
            types::I64,
            stack_slot,
            func.stack_max as i32 + func.locals as i32,
        );

        self.builder
            .ins()
            .stack_store(stack, frame_slot, offset_of!(Frame, stack) as i32);
        self.builder
            .ins()
            .stack_store(locals, frame_slot, offset_of!(Frame, locals) as i32);
        self.builder
            .ins()
            .stack_store(upvalues, frame_slot, offset_of!(Frame, upvalues) as i32);
        let frame = self.builder.ins().stack_addr(types::I64, frame_slot, 0);
        let prev = self.builder.ins().load(
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
        );
        
    }
}
