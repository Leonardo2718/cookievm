/*

Copyright (C) 2018 Leonardo Banderali

License:

    Permission is hereby granted, free of charge, to any person obtaining a copy
    of this software and associated documentation files (the "Software"), to deal
    in the Software without restriction, including without limitation the rights
    to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
    copies of the Software, and to permit persons to whom the Software is
    furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be included in
    all copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
    AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
    THE SOFTWARE.

*/

use cookie_base as cookie;
use interpreter::*;
use std::collections::HashMap;

#[derive(Debug,Clone,PartialEq)]
enum DebugState {
    Running, // program is running (in debugger)
    Paused,  // program execution is paused
}

/*
The `Thread` struct handles execution of Cookie code.
*/
pub struct Thread {
    interp: Interpreter,
    status: Status,
    debug_state: DebugState,
}

impl Thread {
    pub fn new(instructions: cookie::InstructionList) -> Thread {
        Thread  { interp: Interpreter::new(instructions)
                , status: Status::Ok
                , debug_state: DebugState::Paused
                }
    }

    pub fn exec(&mut self) -> Result<Option<cookie::Value>> {
        loop {
            self.status = self.interp.exec_next()?; 
            if self.status == Status::Finish { break; }
        }
        return Ok(self.interp.stack.pop());
    }

    // debugger ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    pub fn debug(&mut self) -> Result<()> {
        use std::cmp;
        use rustyline::error::ReadlineError;
        use rustyline::Editor;

        let mut prompt = Editor::<()>::new();  // command-line style prompt

        macro_rules! debug_quit {
            () => ({
                if self.status == Status::Finish { break; }
                else {
                    let readline = prompt.readline("Program thread is still running, are you sure you want to quit (y/n): ");
                    match readline {
                        Ok(ref r) if r == "y" => return Err(InterpreterError::DebuggerError("Program terminated by user.".to_string())),
                        _ => continue,
                    }
                }
            })
        }

        macro_rules! stack_point {
            ($pos:expr) => (
                if $pos == self.interp.stack.len() && $pos == self.interp.fp { "<= $sp, $fp" }
                else if $pos == self.interp.fp { "<= $fp" }
                else if $pos == self.interp.stack.len() { "<= $sp" }
                else { "" }
            )
        }

        macro_rules! print_stack {
            () => ({
                for (pos, val) in self.interp.stack.iter().enumerate().rev() {
                    let pos = pos + 1;
                    let point = stack_point!(pos);
                    println!("0x{:08x} {:12}{}", pos, val.to_string(), point);
                }
                println!("----------");
                println!("0x{:08x} {:12}{}", 0, cookie::Value::Void.to_string(), stack_point!(0));
            })
        }

        macro_rules! list_insts {
            ($addr:expr) => ({
                let start = if $addr < 2 { $addr } else { $addr - 2 };
                let end = cmp::min(self.interp.instructions.len(), $addr + 3);
                for i in start..end {
                    let pointer = if i == self.interp.pc {"$pc => "} else { "       " };
                    println!("{}0x{:08x} {:?}", pointer, i, self.interp.instructions[i]);
                }
            })
        }

        loop {
            if self.debug_state == DebugState::Running {
                if self.interp.pc >= self.interp.instructions.len() { self.debug_state = DebugState::Paused; continue; }
                match self.interp.exec_next() {
                    Err(msg) => { println!("{}", msg); self.debug_state = DebugState::Paused; }
                    _ => continue,
                };
            } else {
                let readline = prompt.readline(">> ");
                match readline {
                    Ok(cmd) => { prompt.add_history_entry(cmd.as_ref()); match cmd.as_ref() {
                        "l" | "list" => list_insts!(self.interp.pc),
                        "bt" | "stack" | "backtrace" => print_stack!(),
                        "c" | "continue" | "r" | "run" => self.debug_state = DebugState::Running,
                        "s" | "step" => { self.interp.exec_next()?; }
                        "q" | "quit" => debug_quit!(),
                        _ => println!("Error: unknown command {:?}", cmd),
                    };},
                    Err(ReadlineError::Eof) => continue,
                    Err(ReadlineError::Interrupted) => continue,
                    Err(_) => break,
                };
            }
        }

        return Ok(());
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::cookie::*;
    use super::cookie::Instruction::*;
    use super::cookie::Target::*;

    #[test]
    fn pushc_test_1() {
        let insts = vec![
            PUSHC(Value::I32(3)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(3));
    }

    #[test]
    fn pushc_test_2() {
        let insts = vec![
            PUSHC(Value::F32(3.14159)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::F32(3.14159));
    }

    #[test]
    fn pushc_test_3() {
        let insts = vec![
            PUSHC(Value::Bool(true)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::Bool(true));
    }

    #[test]
    fn pushc_test_4() {
        let insts = vec![
            PUSHC(Value::Char('w')),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::Char('w'));
    }

    #[test]
    fn pushc_test_5() {
        let insts = vec![
            PUSHC(Value::IPtr(0x5)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::IPtr(0x5));
    }

    #[test]
    fn pushc_test_6() {
        let insts = vec![
            PUSHC(Value::SPtr(0x5)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::SPtr(0x5));
    }

    #[test]
    fn pushc_test_7() {
        let insts = vec![
            PUSHC(Value::Void),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::Void);
    }

    #[test]
    fn pop_test_1() {
        let insts = vec![
            PUSHC(Value::I32(2)),
            POP,
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().unwrap().is_none());
    }

    #[test]
    fn pop_test_2() {
        let insts = vec![
            PUSHC(Value::F32(2.71828)),
            POP,
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().unwrap().is_none());
    }

    #[test]
    fn pop_test_3() {
        let insts = vec![
            PUSHC(Value::Bool(true)),
            POP,
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().unwrap().is_none());
    }

    #[test]
    fn pop_test_4() {
        let insts = vec![
            PUSHC(Value::Void),
            POP,
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().unwrap().is_none());
    }

    #[test]
    fn binop_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::I32(2)),
            BOp(BinaryOp::ADD, Loc::Stack, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(3));
    }

    #[test]
    fn binop_test_2() {
        let insts = vec![
            PUSHC(Value::IPtr(0x7ab)),
            PUSHC(Value::I32(4)),
            BOp(BinaryOp::SUB, Loc::Stack, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::IPtr(0x7a7));
    }

    #[test]
    fn binop_test_3() {
        let insts = vec![
            PUSHC(Value::F32(4.0)),
            PUSHC(Value::I32(4)),
            BOp(BinaryOp::ADD, Loc::Stack, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn binop_test_4() {
        let insts = vec![
            PUSHC(Value::Void),
            PUSHC(Value::I32(4)),
            BOp(BinaryOp::MUL, Loc::Stack, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn uniop_test_1() {
        let insts = vec![
            PUSHC(Value::I32(3)),
            UOp(UnaryOp::NEG, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-3));
    }

    #[test]
    fn uniop_test_2() {
        let insts = vec![
            PUSHC(Value::F32(2.71828)),
            UOp(UnaryOp::NEG, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::F32(-2.71828));
    }

    #[test]
    fn uniop_test_3() {
        let insts = vec![
            PUSHC(Value::Bool(false)),
            UOp(UnaryOp::NOT, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::Bool(true));
    }

    #[test]
    fn uniop_test_4() {
        let insts = vec![
            PUSHC(Value::I32(0)),
            UOp(UnaryOp::NOT, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn uniop_test_5() {
        let insts = vec![
            PUSHC(Value::Void),
            UOp(UnaryOp::NOT, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn uniop_test_6() {
        let insts = vec![
            PUSHC(Value::F32(3.14)),
            UOp(UnaryOp::CVT(Type::I32), Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(3));
    }

    #[test]
    fn pushr_test_1() {
        let insts = vec![
            PUSHR(RegisterName::StackPointer),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::SPtr(0));
    }

    #[test]
    fn pushr_test_2() {
        let insts = vec![
            PUSHC(Value::I32(3)),
            PUSHC(Value::F32(3.14159)),
            PUSHC(Value::Char('c')),
            PUSHR(RegisterName::StackPointer),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::SPtr(3));
    }

    #[test]
    fn pushr_test_3() {
        let insts = vec![
            PUSHC(Value::I32(3)),
            PUSHC(Value::F32(3.14159)),
            PUSHC(Value::Char('c')),
            POP,
            PUSHR(RegisterName::StackPointer),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::SPtr(2));
    }

    #[test]
    fn pushr_test_4() {
        let insts = vec![
            PUSHR(RegisterName::ProgramCounter),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::IPtr(0));
    }

    #[test]
    fn pushr_test_5() {
        let insts = vec![
            PUSHC(Value::I32(3)),
            PUSHC(Value::F32(3.14159)),
            PUSHC(Value::Char('c')),
            PUSHR(RegisterName::ProgramCounter),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::IPtr(3));
    }

    #[test]
    fn pushr_test_6() {
        let insts = vec![
            PUSHC(Value::I32(3)),
            PUSHC(Value::F32(3.14159)),
            PUSHC(Value::Char('c')),
            POP,
            PUSHR(RegisterName::ProgramCounter),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::IPtr(4));
    }

    #[test]
    fn popr_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::I32(2)),
            PUSHC(Value::I32(3)),
            PUSHC(Value::I32(4)),
            PUSHC(Value::SPtr(2)),
            POPR(RegisterName::StackPointer),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(2));
    }

    #[test]
    fn popr_test_2() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            POPR(RegisterName::StackPointer),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn popr_test_3() {
        let insts = vec![
            PUSHC(Value::IPtr(0x0)),
            POPR(RegisterName::StackPointer),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn popr_test_4() {
        let insts = vec![
            PUSHC(Value::SPtr(0x2)),
            POPR(RegisterName::ProgramCounter),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn jump_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            JUMP(InternalLabel(4, "label".to_string())),
            POP,
            PUSHC(Value::I32(2)),
            UOp(UnaryOp::NEG, Loc::Stack, Loc::Stack),
        ];
        let mut labels: LabelTable = HashMap::new();
        labels.insert("label".to_string(), 4);
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn jump_test_2() {
        let insts = vec![
            JUMP(UnresolvedLabel("label".to_string())),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn djump_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::IPtr(5)),
            DJUMP(Loc::Stack),
            POP,
            PUSHC(Value::Void),
            UOp(UnaryOp::NEG, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn djump_test_2() {
        let insts = vec![
            PUSHC(Value::I32(0)),
            DJUMP(Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn branchon_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::Bool(true)),
            BRANCHON(Value::Bool(true), InternalLabel(5, "label".to_string()), Loc::Stack),
            POP,
            PUSHC(Value::Void),
            UOp(UnaryOp::NEG, Loc::Stack, Loc::Stack),
        ];
        let mut labels: LabelTable = HashMap::new();
        labels.insert("label".to_string(), 5);
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn branchon_test_2() {
        let insts = vec![
            PUSHC(Value::Void),
            PUSHC(Value::Bool(true)),
            BRANCHON(Value::Bool(false), InternalLabel(5, "label".to_string()), Loc::Stack),
            POP,
            PUSHC(Value::I32(-1)),
            UOp(UnaryOp::NEG, Loc::Stack, Loc::Stack),
        ];
        let mut labels: LabelTable = HashMap::new();
        labels.insert("label".to_string(), 5);
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(1));
    }

    #[test]
    fn branchon_test_3() {
        let insts = vec![
            PUSHC(Value::Void),
            PUSHC(Value::Bool(true)),
            BRANCHON(Value::I32(1), InternalLabel(5, "label".to_string()), Loc::Stack),
            POP,
            PUSHC(Value::I32(-1)),
            UOp(UnaryOp::NEG, Loc::Stack, Loc::Stack),
        ];
        let mut labels: LabelTable = HashMap::new();
        labels.insert("label".to_string(), 5);
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn loadfrom_test_1() {
        let insts = vec![
            PUSHC(Value::I32(2)),
            PUSHR(RegisterName::StackPointer),
            LOADFROM(Loc::Stack, Loc::Stack),
            BOp(BinaryOp::ADD, Loc::Stack, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(4));
    }

    #[test]
    fn loadfrom_test_2() {
        let insts = vec![
            PUSHC(Value::I32(2)),
            PUSHC(Value::I32(1)),
            LOADFROM(Loc::Stack, Loc::Stack),
            BOp(BinaryOp::ADD, Loc::Stack, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn storeto_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::I32(1)),
            PUSHC(Value::I32(0)),
            PUSHC(Value::SPtr(0x1)),
            STORETO(Loc::Stack, Loc::Stack),
            BOp(BinaryOp::ADD, Loc::Stack, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(1));
    }

    #[test]
    fn storeto_test_2() {
        let insts = vec![
            PUSHC(Value::I32(2)),
            PUSHC(Value::I32(1)),
            STORETO(Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }
}