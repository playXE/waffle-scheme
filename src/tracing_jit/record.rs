use std::mem::size_of;

use super::trace_ir::*;
use crate::{
    compiler::Op,
    runtime::{value::Value, SchemeThread},
};

pub enum RecordResult {
    Fail(FailReason),
    Ok,
}

pub enum FailReason {
    TraceTooBig,
    Error(Value),
}

const TRACE_LIMIT: usize = 1000;

pub unsafe fn record_loop(
    thread: &mut SchemeThread,
    trace: &mut Vec<(Trace, u32)>,
    start_of_trace: usize,
) -> RecordResult {
    let mut frame = &mut *thread.vm_stack.current_frame;
    macro_rules! emit {
        ($ins: expr) => {
            if trace.len() > TRACE_LIMIT {
                return RecordResult::Fail(FailReason::TraceTooBig);
            }
            trace.push(($ins, frame.ip as u32));
        };
        ($ins: expr, $ip: expr) => {
            if trace.len() > TRACE_LIMIT {
                return RecordResult::Fail(FailReason::TraceTooBig);
            }
            trace.push(($ins, $ip as u32));
        };
    }
    loop {
        let code = std::slice::from_raw_parts(
            frame.code.unwrap_unchecked().as_ptr().cast::<Op>(),
            frame.code.unwrap_unchecked().len() / size_of::<Op>(),
        );

        match &code[frame.ip..] {
            [Op::PushTrue, Op::JumpIfFalse(_), ..]
            | [Op::PushInt(_), Op::JumpIfFalse(_), ..]
            | [Op::PushConstant(_), Op::JumpIfFalse(_), ..] => {
                frame.ip += 2;
            }

            [Op::PushInt(x), ..] => {
                emit!(Trace::PushInt(*x));
                frame.ip += 1;
            }
            [Op::PushConstant(x), Op::CloseOver] => {
                emit!(Trace::CloseOver(*x));
                frame.ip += 2;
            }

            [Op::PushNull, Op::JumpIfFalse(ip), ..] => frame.ip = *ip as usize,
            [Op::PushFalse, Op::JumpIfFalse(ip), ..] => {
                frame.ip = *ip as usize;
            }
            [Op::JumpIfFalse(ip), ..] => {
                let value = frame.pop();
                frame.ip += 1;
                if !value.to_boolean() {
                    emit!(Trace::GuardFalse(frame.ip as u32));
                } else {
                    emit!(Trace::GuardTrue(*ip));
                }
            }
            [Op::Jump(ip), ..] => {
                frame.ip = *ip as usize;
                if *ip == start_of_trace as u32 {
                    emit!(Trace::LinkLoop);

                    return RecordResult::Ok;
                }
            }

            _ => todo!(),
        }
    }
}
