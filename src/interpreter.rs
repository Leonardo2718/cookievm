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
use std::io;
use std::io::Read;
use std::io::Write;

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
            LOADFROM(dest, src) => {
                let addr = expect_value!(self.get_value(src)?, SPtr, "Cannot load from non-SPtr value {bad_value}")?;
                let val = self.stack[addr - 1];
                self.put_value(dest, val)?;
                self.pc + 1
            },
            STORETO(dest, src) => {
                let addr = expect_value!(self.get_value(dest)?, SPtr, "Cannot load from non-SPtr value {bad_value}")?;
                let val = self.get_value(src)?;
                self.stack[addr - 1] = val;
                self.pc + 1
            },
            UOp(op, dest, src) =>  {
                let val = self.get_value(src)?;
                let res = op.apply_to(val)?;
                self.put_value(dest, res)?;
                self.pc + 1
            },
            BOp(op, dest, lhs, rhs) => {
                let rhs_v = self.get_value(rhs)?;
                let lhs_v = self.get_value(lhs)?;
                let res = op.apply_to(lhs_v, rhs_v)?;
                self.put_value(dest, res)?;
                self.pc + 1
            },
            JUMP(label) => *self.get_label(label)?,
            DJUMP(src) => {
                expect_value!(self.get_value(src)?, IPtr, "Cannot jump to non-IPtr value {bad_value}")?
            },
            BRANCHON(imm, label, src) => {
                let val = self.get_value(src)?;
                let condition = expect_value!(cookie::BinaryOp::EQ.apply_to(*imm, val)?, Bool, "Failed to evaluate branch condition; got {bad_value}")?;
                if condition { *self.get_label(label)? } else { self.pc + 1 }
            },
            PRINT(src) => {
                use self::cookie::Value::*;
                let s = match self.get_value(src)? {
                    Char(c) => format!("{}", c),
                    I32(i) => format!("{}", i),
                    F32(f) => format!("{}", f),
                    Bool(b) => format!("{}", b),
                    v => format!("{}", v)
                };
                {
                    let stdout = io::stdout();
                    let mut handle = stdout.lock();
                    handle.write(s.as_bytes()).map_err(|e| e.to_string())?;
                    handle.flush().map_err(|e| e.to_string())?;
                }
                self.pc + 1
            },
            READ(t, dest) => {
                use self::cookie::Value;
                use self::cookie::Type;

                macro_rules! read_val {
                    ($t:tt) => ({
                        let mut input = String::new();
                        io::stdin().read_line(&mut input).map_err(|e| e.to_string())?;
                        input.trim().parse::<$t>().map_err(|e| e.to_string())?
                    })
                }

                // macro_rules! read

                let val = match t {
                    &Type::I32 => Value::I32(read_val!(i32)),
                    &Type::F32 => Value::F32(read_val!(f32)),
                    &Type::Bool => Value::Bool(read_val!(bool)),
                    &Type::Char => {
                        let mut input = String::new();
                        io::stdin().read_line(&mut input).map_err(|e| e.to_string())?;
                        Value::Char(input.chars().nth(0).unwrap())
                    }
                    _ => return Err(format!("Cannot do read of time: {}", t))
                };
                self.put_value(dest, val)?;
                self.pc + 1
            },
            EXIT => { self.instructions.len() } // setting pc to past the end will force termination
            _ => panic!("Unimplemented instruction: {:?}", inst)
        };
        return Ok(());
    }

    fn do_pushr(&mut self, reg: &cookie::RegisterName) -> Result<(), String> {
        let val = self.register_get(*reg)?;
        self.stack.push(val);
        Ok(())
    }

    fn do_popr(&mut self, reg: &cookie::RegisterName) -> Result<(), String> {
        let val = self.pop()?;
        self.register_put(*reg, val)?;
        Ok(())
    }

    fn get_value(&mut self, loc: &cookie::Loc) -> Result<cookie::Value, String> {
        use self::cookie::Loc;
        match loc {
            Loc::Stack => self.pop(),
            Loc::Reg(r) => self.register_get(*r),
        }
    }

    fn put_value(&mut self, loc: &cookie::Loc, val: cookie::Value) -> Result<(), String> {
        use self::cookie::Loc;
        match loc {
            Loc::Stack => { self.stack.push(val); Ok(()) },
            Loc::Reg(r) => self.register_put(*r, val),
        }
    }

    fn register_get(&mut self, reg: cookie::RegisterName) -> Result<cookie::Value, String> {
        use self::cookie::Value;
        use self::cookie::RegisterName;
        match reg {
            RegisterName::StackPointer => Ok(Value::SPtr(self.stack.len())),
            RegisterName::FramePointer => Ok(Value::SPtr(self.fp)),
            RegisterName::ProgramCounter => Ok(Value::IPtr(self.pc)),
            _ => Err(format!("Unimplemented register access: {}", reg))
        }
    }

    fn register_put(&mut self, reg: cookie::RegisterName, val: cookie::Value) -> Result<(), String> {
        use self::cookie::Value;
        use self::cookie::RegisterName;
        match reg {
            RegisterName::StackPointer => {
                let v = expect_value!(val, SPtr, "Expecting SPtr value but got {bad_value} instead.")?;
                self.stack.resize(v, Value::Void);
                Ok(())
            }
            RegisterName::FramePointer => {
                let v = expect_value!(val, SPtr, "Expecting SPtr value but got {bad_value} instead.")?;
                self.fp = v;
                Ok(())
            }
            RegisterName::ProgramCounter => {
                self.pc = expect_value!(val, IPtr, "Expecting IPtr value but got {bad_value} instead")?;
                Ok(())
            }
            _ => Err(format!("Unimplemented register access {}", reg))
        }
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
            BOp(BinaryOp::ADD, Loc::Stack, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(3));
    }

    #[test]
    fn binop_test_2() {
        let insts = vec![
            PUSHC(Value::IPtr(0x7ab)),
            PUSHC(Value::I32(4)),
            BOp(BinaryOp::SUB, Loc::Stack, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::IPtr(0x7a7));
    }

    #[test]
    fn binop_test_3() {
        let insts = vec![
            PUSHC(Value::F32(4.0)),
            PUSHC(Value::I32(4)),
            BOp(BinaryOp::ADD, Loc::Stack, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().is_err());
    }

    #[test]
    fn binop_test_4() {
        let insts = vec![
            PUSHC(Value::Void),
            PUSHC(Value::I32(4)),
            BOp(BinaryOp::MUL, Loc::Stack, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().is_err());
    }

    #[test]
    fn uniop_test_1() {
        let insts = vec![
            PUSHC(Value::I32(3)),
            UOp(UnaryOp::NEG, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-3));
    }

    #[test]
    fn uniop_test_2() {
        let insts = vec![
            PUSHC(Value::F32(2.71828)),
            UOp(UnaryOp::NEG, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::F32(-2.71828));
    }

    #[test]
    fn uniop_test_3() {
        let insts = vec![
            PUSHC(Value::Bool(false)),
            UOp(UnaryOp::NOT, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::Bool(true));
    }

    #[test]
    fn uniop_test_4() {
        let insts = vec![
            PUSHC(Value::I32(0)),
            UOp(UnaryOp::NOT, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn uniop_test_5() {
        let insts = vec![
            PUSHC(Value::Void),
            UOp(UnaryOp::NOT, Loc::Stack, Loc::Stack),
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
            UOp(UnaryOp::NEG, Loc::Stack, Loc::Stack),
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
    fn djump_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::IPtr(5)),
            DJUMP(Loc::Stack),
            POP,
            PUSHC(Value::Void),
            UOp(UnaryOp::NEG, Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn djump_test_2() {
        let insts = vec![
            PUSHC(Value::I32(0)),
            DJUMP(Loc::Stack),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().is_err());
    }

    #[test]
    fn branchon_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::Bool(true)),
            BRANCHON(Value::Bool(true), "label".to_string(), Loc::Stack),
            POP,
            PUSHC(Value::Void),
            UOp(UnaryOp::NEG, Loc::Stack, Loc::Stack),
        ];
        let mut labels: LabelTable = HashMap::new();
        labels.insert("label".to_string(), 5);
        let mut thread = Thread::new(&insts, labels);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn branchon_test_2() {
        let insts = vec![
            PUSHC(Value::Void),
            PUSHC(Value::Bool(true)),
            BRANCHON(Value::Bool(false), "label".to_string(), Loc::Stack),
            POP,
            PUSHC(Value::I32(-1)),
            UOp(UnaryOp::NEG, Loc::Stack, Loc::Stack),
        ];
        let mut labels: LabelTable = HashMap::new();
        labels.insert("label".to_string(), 5);
        let mut thread = Thread::new(&insts, labels);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(1));
    }

    #[test]
    fn branchon_test_3() {
        let insts = vec![
            PUSHC(Value::Void),
            PUSHC(Value::Bool(true)),
            BRANCHON(Value::I32(1), "label".to_string(), Loc::Stack),
            POP,
            PUSHC(Value::I32(-1)),
            UOp(UnaryOp::NEG, Loc::Stack, Loc::Stack),
        ];
        let mut labels: LabelTable = HashMap::new();
        labels.insert("label".to_string(), 5);
        let mut thread = Thread::new(&insts, labels);
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
        let mut thread = Thread::new(&insts, HashMap::new());
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
        let mut thread = Thread::new(&insts, HashMap::new());
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
        let mut thread = Thread::new(&insts, HashMap::new());
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(1));
    }

    #[test]
    fn storeto_test_2() {
        let insts = vec![
            PUSHC(Value::I32(2)),
            PUSHC(Value::I32(1)),
            STORETO(Loc::Stack, Loc::Stack),
        ];
        let mut thread = Thread::new(&insts, HashMap::new());
        assert!(thread.exec().is_err());
    }
}
