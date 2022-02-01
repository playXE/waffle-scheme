use std::ptr::null_mut;

use crate::compiler::Op;

use super::{value::Value, vm::Frame};

pub struct Interpreter {
    stack: Box<[Value]>,
    current_frame: *mut Frame,
    sp: *mut Value,
    end: *mut Value,
}

impl Interpreter {
    pub unsafe fn allocate(&mut self, values: usize) -> *mut Value {
        let result = self.sp;
        let new_sp = self.sp.add(values);
        if new_sp >= self.end {
            return null_mut();
        }
        result
    }
}
