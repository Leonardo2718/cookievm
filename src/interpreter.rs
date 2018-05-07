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
use std::collections::HashMap;

pub type InstructionList = Vec<cookie::Instruction>;
pub type Stack = Vec<cookie::Value>;
pub type LabelTable = HashMap<String, usize>;

/*
The `Thread` struct handles execution of Cookie code.
*/
pub struct Thread<'a> {
    instructions: &'a InstructionList,
    stack: Stack,
    fp: usize,
    pc: usize,
    gpr: [cookie::Value; 16],
    label_table: LabelTable,
}

macro_rules! expect_value {
    ($expr:expr, $ctor:ident, $($args:tt),+) => (
        match $expr {
            cookie::Value::$ctor(v) => Ok(v),
            v => Err(format!($($args),+, bad_value = v))
        }
    )
}

impl<'a> Thread<'a> {
    pub fn new(instructions: &'a InstructionList, labels: LabelTable) -> Thread<'a> {
        use self::cookie::Value;
        Thread  { instructions: instructions
                , stack: Vec::new()
                , fp: 0
                , pc: 0
                , gpr: [Value::Void; 16]
                , label_table: labels
                }
    }

    pub fn exec(&mut self) -> Result<Option<cookie::Value>, String> {
        while self.pc < self.instructions.len() {
            let inst =  &self.instructions[self.pc];
            self.exec_instruction(&inst)?;
        }
        return Ok(self.stack.pop());
    }

    fn exec_instruction(&mut self, inst: &cookie::Instruction) -> Result<(), String> {
        use cookie_base::Instruction::*;
        self.pc = match inst {
            PUSHR(reg) => {
                self.do_pushr(reg)?;
                self.pc + 1
            },
            PUSHC(v) => {
                self.stack.push(v.clone());
                self.pc + 1
            },
            POPR(reg) => {
                self.do_popr(reg)?;
                self.pc + 1
            },
            POP => { self.pop()?; self.pc + 1 },
            LOADATS => {
                let loc = expect_value!(self.pop()?, SPtr, "Cannot load from non-SPtr value {bad_value}")?;
                let val = self.stack[loc];
                self.stack.push(val);
                self.pc + 1
            },
            STACK_BINARY(op) => {
                let rhs = self.pop()?;
                let lhs = self.pop()?;
                let res = op.apply_to(lhs, rhs)?;
                self.stack.push(res);
                self.pc + 1
            },
            STACK_UNARY(op) => {
                let val = self.pop()?;
                let res = op.apply_to(val)?;
                self.stack.push(res);
                self.pc + 1
            },
            JUMP(label) => *self.get_label(label)?,
            JUMPS => expect_value!(self.pop()?, IPtr, "Cannot jump to non-IPtr value {bad_value}")?,
            BRANCHONS(ival, label) => {
                let sval = self.pop()?;
                let condition = expect_value!(cookie::BOp::EQ.apply_to(*ival, sval)?, Bool, "Failed to evaluate branch condition; got {bad_value}")?;
                if condition { *self.get_label(label)? } else { self.pc + 1 }
            },
            PRINTS => { self.do_print()?; self.pc + 1 },
            EXIT => { self.instructions.len() } // setting pc to past the end will force termination
            _ => panic!("Unimplemented instruction: {:?}", inst)
        };
        return Ok(());
    }

    fn do_pushr(&mut self, reg: &cookie::RegisterName) -> Result<(), String> {
        use self::cookie::Value;
        use self::cookie::RegisterName;
        match reg {
            RegisterName::StackPointer => {
                let top = self.stack.len();
                self.stack.push(Value::SPtr(top)); },
            RegisterName::ProgramCounter => self.stack.push(Value::IPtr(self.pc)),
            _ => panic!("Unimplemented register access: {:?}", reg)
        };
        return Ok(());
    }

    fn do_popr(&mut self, reg: &cookie::RegisterName) -> Result<(), String> {
        use self::cookie::Value;
        use self::cookie::RegisterName;
        match reg {
            RegisterName::StackPointer => {
                let v = self.pop()?;
                self.stack.resize(expect_value!(v, SPtr, "Expecting SPtr value on stack but got {bad_value} instead.")?, Value::Void);
            }
            RegisterName::ProgramCounter => {
                let v = self.pop()?;
                self.pc = expect_value!(v, IPtr, "Expecting IPtr value on stack but got {bad_value} instead")?;
            }
            _ => panic!("Unimplemented register access {:?}", reg)
        }
        return Ok(());
    }

    fn do_print(&mut self) -> Result<(), String> {
        let v = self.pop()?;
        print!("{}", v.value_as_str());
        Ok(())
    }

    fn pop(&mut self) -> Result<cookie::Value, String> {
        self.stack.pop().ok_or("Cannot pop value from stack: stack is empty.".to_string())
    }

    fn get_label(&self, label: &str) -> cookie::Result<&usize> {
        self.label_table.get(label).ok_or(format!("No label with name {}", label)).clone()
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use super::cookie::*;
    use super::cookie::Instruction::*;

    #[test]
    fn pushc_test_1() {
        let insts = vec![
            PUSHC(Value::I32(3)),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(3));
    }

    #[test]
    fn pushc_test_2() {
        let insts = vec![
            PUSHC(Value::F32(3.14159)),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::F32(3.14159));
    }

    #[test]
    fn pushc_test_3() {
        let insts = vec![
            PUSHC(Value::Bool(true)),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::Bool(true));
    }

    #[test]
    fn pushc_test_4() {
        let insts = vec![
            PUSHC(Value::Char('w')),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::Char('w'));
    }

    #[test]
    fn pushc_test_5() {
        let insts = vec![
            PUSHC(Value::IPtr(0x5)),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::IPtr(0x5));
    }

    #[test]
    fn pushc_test_6() {
        let insts = vec![
            PUSHC(Value::SPtr(0x5)),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::SPtr(0x5));
    }

    #[test]
    fn pushc_test_7() {
        let insts = vec![
            PUSHC(Value::Void),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::Void);
    }

    #[test]
    fn pop_test_1() {
        let insts = vec![
            PUSHC(Value::I32(2)),
            POP,
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().unwrap().is_none());
    }

    #[test]
    fn pop_test_2() {
        let insts = vec![
            PUSHC(Value::F32(2.71828)),
            POP,
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().unwrap().is_none());
    }

    #[test]
    fn pop_test_3() {
        let insts = vec![
            PUSHC(Value::Bool(true)),
            POP,
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().unwrap().is_none());
    }

    #[test]
    fn pop_test_4() {
        let insts = vec![
            PUSHC(Value::Void),
            POP,
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().unwrap().is_none());
    }

    #[test]
    fn binop_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::I32(2)),
            STACK_BINARY(BOp::ADD),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(3));
    }

    #[test]
    fn binop_test_2() {
        let insts = vec![
            PUSHC(Value::IPtr(0x7ab)),
            PUSHC(Value::I32(4)),
            STACK_BINARY(BOp::SUB),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::IPtr(0x7a7));
    }

    #[test]
    fn binop_test_3() {
        let insts = vec![
            PUSHC(Value::F32(4.0)),
            PUSHC(Value::I32(4)),
            STACK_BINARY(BOp::ADD),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().is_err());
    }

    #[test]
    fn binop_test_4() {
        let insts = vec![
            PUSHC(Value::Void),
            PUSHC(Value::I32(4)),
            STACK_BINARY(BOp::MUL),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().is_err());
    }

    #[test]
    fn uniop_test_1() {
        let insts = vec![
            PUSHC(Value::I32(3)),
            STACK_UNARY(UOp::NEG),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-3));
    }

    #[test]
    fn uniop_test_2() {
        let insts = vec![
            PUSHC(Value::F32(2.71828)),
            STACK_UNARY(UOp::NEG),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::F32(-2.71828));
    }

    #[test]
    fn uniop_test_3() {
        let insts = vec![
            PUSHC(Value::Bool(false)),
            STACK_UNARY(UOp::NOT),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::Bool(true));
    }

    #[test]
    fn uniop_test_4() {
        let insts = vec![
            PUSHC(Value::I32(0)),
            STACK_UNARY(UOp::NOT),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn uniop_test_5() {
        let insts = vec![
            PUSHC(Value::Void),
            STACK_UNARY(UOp::NOT),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().is_err());
    }

    #[test]
    fn pushr_test_1() {
        let insts = vec![
            PUSHR(RegisterName::StackPointer),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
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
        let mut thread = Thread::new(&insts, HashMap::new());
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
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::SPtr(2));
    }

    #[test]
    fn pushr_test_4() {
        let insts = vec![
            PUSHR(RegisterName::ProgramCounter),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
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
        let mut thread = Thread::new(&insts, HashMap::new());
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
        let mut thread = Thread::new(&insts, HashMap::new());
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
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(2));
    }

    #[test]
    fn popr_test_2() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            POPR(RegisterName::StackPointer),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().is_err());
    }

    #[test]
    fn popr_test_3() {
        let insts = vec![
            PUSHC(Value::IPtr(0x0)),
            POPR(RegisterName::StackPointer),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().is_err());
    }

    #[test]
    fn popr_test_4() {
        let insts = vec![
            PUSHC(Value::SPtr(0x2)),
            POPR(RegisterName::ProgramCounter),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().is_err());
    }

    #[test]
    fn jump_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            JUMP("label".to_string()),
            POP,
            PUSHC(Value::I32(2)),
            STACK_UNARY(UOp::NEG),
        ];
        let mut labels: LabelTable = HashMap::new();
        labels.insert("label".to_string(), 4);
        let mut thread = Thread::new(&insts, labels);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn jump_test_2() {
        let insts = vec![
            JUMP("label".to_string()),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().is_err());
    }

    #[test]
    fn jumps_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::IPtr(5)),
            JUMPS,
            POP,
            PUSHC(Value::Void),
            STACK_UNARY(UOp::NEG),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn jumps_test_2() {
        let insts = vec![
            PUSHC(Value::I32(0)),
            JUMPS,
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().is_err());
    }

    #[test]
    fn branchons_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::Bool(true)),
            BRANCHONS(Value::Bool(true), "label".to_string()),
            POP,
            PUSHC(Value::Void),
            STACK_UNARY(UOp::NEG),
        ];
        let mut labels: LabelTable = HashMap::new();
        labels.insert("label".to_string(), 5);
        let mut thread = Thread::new(&insts, labels);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn branchons_test_2() {
        let insts = vec![
            PUSHC(Value::Void),
            PUSHC(Value::Bool(true)),
            BRANCHONS(Value::Bool(false), "label".to_string()),
            POP,
            PUSHC(Value::I32(-1)),
            STACK_UNARY(UOp::NEG),
        ];
        let mut labels: LabelTable = HashMap::new();
        labels.insert("label".to_string(), 5);
        let mut thread = Thread::new(&insts, labels);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(1));
    }

    #[test]
    fn branchons_test_3() {
        let insts = vec![
            PUSHC(Value::Void),
            PUSHC(Value::Bool(true)),
            BRANCHONS(Value::I32(1), "label".to_string()),
            POP,
            PUSHC(Value::I32(-1)),
            STACK_UNARY(UOp::NEG),
        ];
        let mut labels: LabelTable = HashMap::new();
        labels.insert("label".to_string(), 5);
        let mut thread = Thread::new(&insts, labels);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn loadats_test_1() {
        let insts = vec![
            PUSHC(Value::I32(2)),
            PUSHR(RegisterName::StackPointer),
            PUSHC(Value::I32(1)),
            STACK_BINARY(BOp::SUB),
            LOADATS,
            STACK_BINARY(BOp::ADD),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(4));
    }

    #[test]
    fn loadats_test_2() {
        let insts = vec![
            PUSHC(Value::I32(2)),
            PUSHC(Value::I32(1)),
            PUSHC(Value::I32(1)),
            STACK_BINARY(BOp::SUB),
            LOADATS,
            STACK_BINARY(BOp::ADD),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().is_err());
    }
}
