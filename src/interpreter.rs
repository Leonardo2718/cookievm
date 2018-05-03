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

pub type InstructionList = Vec<cookie::Instruction>;
pub type Stack = Vec<cookie::Value>;

/*
The `Thread` struct handles execution of Cookie code.
*/
pub struct Thread<'a> {
    instructions: &'a InstructionList,
    stack: Stack,
    fp: usize,
    pc: usize,
}

impl<'a> Thread<'a> {
    pub fn new(instructions: &'a InstructionList) -> Thread<'a> {
        Thread { instructions: instructions, stack: Vec::new(), fp: 0, pc: 0 }
    }

    pub fn exec(&mut self) -> Result<Option<cookie::Value>, String> {
        while self.pc < self.instructions.len() {
            let inst =  &self.instructions[self.pc];
            self.exec_instruction(&inst);
        }
        return Ok(None);
    }

    fn exec_instruction(&mut self, inst: &cookie::Instruction) -> Result<(), String> {
        use cookie_base::Instruction::*;
        match inst {
            PUSHR(reg) => self.do_pushr(reg)?,
            PUSHC(v) => self.stack.push(v.clone()),
            POPR(reg) => self.do_popr(reg)?,
            POP => { self.pop()?; }
            // STACK(op, t) => self.do_stack_op(op, t)?,
            STACK_BINARY(op) => {
                let rhs = self.pop()?;
                let lhs = self.pop()?;
                op.apply(lhs, rhs);
            },
            PRINTS => self.do_print()?,
            _ => panic!("Unimplemented instruction: {:?}", inst)
        };
        self.pc += 1;
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
        use self::cookie::Type;
        use self::cookie::RegisterName;
        match reg {
            RegisterName::StackPointer => {
                match self.pop()? {
                    Value::SPtr(v) => self.stack.resize(v, Value::Void),
                    v => return Err(format!("Expecting {} value on stack but got {} instead.", Type::SPtr, v.get_type()))
                };
            }
            RegisterName::ProgramCounter => {
                match self.pop()? {
                    Value::IPtr(v) => self.pc = v,
                    v => return Err(format!("Expecting {} value on stack but got {} instead.", Type::IPtr, v.get_type()))
                };
            }
            _ => panic!("Unimplemented register access {:?}", reg)
        }
        return Ok(());
    }

    // fn do_stack_op(&mut self, op: &cookie::Operation, t: &cookie::Type) -> Result<(), String> {

    // }

    fn do_print(&mut self) -> Result<(), String> {
        let v = self.pop()?;
        print!("{}", v.value_as_str());
        Ok(())
    }

    fn pop(&mut self) -> Result<cookie::Value, String> {
        self.stack.pop().ok_or("Cannot pop value from stack: stack is empty.".to_string())
    }
}

fn print_stack(stack: &Stack) {
    print!("[");
    for elem in stack {
        print!("{:?}, ", elem);
    }
    println!("]");
}
