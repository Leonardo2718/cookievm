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
use std::io;
use std::io::Write;
use std::fmt;
use std::num;
use std::str;
use std::error;
use std::result;
use std::convert;

#[derive(Debug)]
pub enum InterpreterError {
    AttemptedLoadFromNonSPtr(cookie::Value),
    AttemptedJumpToNonIPtr(cookie::Value),
    TypeMismatchError(cookie::Type,cookie::Value),
    BadInputType(cookie::Type),
    StackUnderflow,
    StackOverflow,
    UndefinedSymbol(String),
    OutOfRangeInstruction(usize),
    DebuggerError(String),
    ParseInputIntError(num::ParseIntError),
    ParseInputFloatError(num::ParseFloatError),
    ParseInputBoolError(str::ParseBoolError),
    OperationError(cookie::OpApplicationError),
    IOError(io::Error),
    UseOfUnimplementedFeature(String),
}

impl fmt::Display for InterpreterError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl error::Error for InterpreterError {
    fn description(&self) -> &str {
        use self::InterpreterError::*;
        match self {
            &AttemptedLoadFromNonSPtr(_) => "Attempted to load value from non-SPtr (non stack address)",
            &AttemptedJumpToNonIPtr(_) => "Attempted to jump to non-IPtr (non instruction address)",
            &TypeMismatchError(_,_) => "Got value of unexpected type",
            &BadInputType(_) => "Cannot read input of given type",
            &StackUnderflow => "Attempted to pop value but stack is empty",
            &StackOverflow => "Attempted to push value but stack is full",
            &UndefinedSymbol(_) => "Attempted to reference a symbol that does not exist",
            &OutOfRangeInstruction(_) => "Attempted to execute instruction at address past the end of instruction sequence",
            &DebuggerError(_) => "Error occured in debugger",
            &ParseInputIntError(_) => "Error parsing input (expecting integral value)",
            &ParseInputFloatError(_) => "Error parsing input (expecting floating-point value)",
            &ParseInputBoolError(_) => "Error parsing input (expecting boolean value)",
            &OperationError(_) => "Error occured while performing operation (see cause)",
            &IOError(_) => "Internal I/O error (see cause)",
            &UseOfUnimplementedFeature(_) => "Attempted to use an unimplemented feature",
        }
    }

    fn cause(&self) -> Option<&error::Error> {
        match self {
            &InterpreterError::ParseInputIntError(ref e) => Some(e),
            &InterpreterError::ParseInputFloatError(ref e) => Some(e),
            &InterpreterError::ParseInputBoolError(ref e) => Some(e),
            &InterpreterError::OperationError(ref e) => Some(e),
            &InterpreterError::IOError(ref e) => Some(e),
            _ => None
        }
    }
}

impl convert::From<cookie::OpApplicationError> for InterpreterError {
    fn from(error: cookie::OpApplicationError) -> Self {
        InterpreterError::OperationError(error)
    }
}

impl convert::From<io::Error> for InterpreterError {
    fn from(error: io::Error) -> Self {
        InterpreterError::IOError(error)
    }
}

impl convert::From<num::ParseIntError> for InterpreterError {
    fn from(error: num::ParseIntError) -> Self {
        InterpreterError::ParseInputIntError(error)
    }
}

impl convert::From<num::ParseFloatError> for InterpreterError {
    fn from(error: num::ParseFloatError) -> Self {
        InterpreterError::ParseInputFloatError(error)
    }
}

impl convert::From<str::ParseBoolError> for InterpreterError {
    fn from(error: str::ParseBoolError) -> Self {
        InterpreterError::ParseInputBoolError(error)
    }
}

pub type Result<T> = result::Result<T, InterpreterError>;

pub type Stack = Vec<cookie::Value>;

/*
Struct encapsulates the environment needed to
execute cookie code
*/
pub struct Interpreter {
    pub instructions: cookie::InstructionList,
    pub stack: Stack,
    pub fp: usize,
    pub pc: usize,
    pub gpr: [cookie::Value; 16],
}

/*
Status of interpreter after executing an instruction
*/
#[derive(Debug,Clone,Copy,PartialEq)]
pub enum Status {
    Ok,     // default normal
    Finish, // normal program termination
}

macro_rules! expect_value {
    ($expr:expr, $ctor:ident, $err:expr) => (
        match $expr {
            cookie::Value::$ctor(v) => Ok(v),
            _v => Err($err)
        }
    )
}

impl Interpreter {
    pub fn new(instructions: cookie::InstructionList) -> Interpreter {
        Interpreter { instructions
                    , stack: Vec::with_capacity(100)
                    , fp: 0
                    , pc: 0
                    , gpr: [cookie::Value::Void; 16]
                    }
    }

    pub fn exec_next(&mut self) -> Result<Status> {
        let inst = self.get_next()?.clone();
        self.exec_instruction(inst)
    }

    fn get_next(&self) -> Result<&cookie::Instruction> {
        self.instructions.get(self.pc).ok_or(InterpreterError::OutOfRangeInstruction(self.pc))
    }

    pub fn exec_instruction(&mut self, inst: cookie::Instruction) -> Result<Status> {
        use cookie_base::Instruction::*;
        self.pc = match inst {
            PUSHR(reg) => { self.do_pushr(reg)?; self.pc + 1 },
            PUSHC(v) => { self.stack.push(v.clone()); self.pc + 1 },
            POPR(reg) => { self.do_popr(reg)?; self.pc + 1 },
            POP => { self.pop()?; self.pc + 1 },
            LOADFROM(dest, src) => {
                let src_val = self.get_value(src)?;
                let addr = expect_value!(src_val, SPtr, InterpreterError::AttemptedLoadFromNonSPtr(src_val))?;
                let val = self.stack[addr - 1];
                self.put_value(dest, val)?;
                self.pc + 1
            },
            STORETO(dest, src) => {
                let dest_val = self.get_value(dest)?;
                let addr = expect_value!(dest_val, SPtr, InterpreterError::AttemptedLoadFromNonSPtr(dest_val))?;
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
            JUMP(symbol) => { self.get_target_addr(&symbol)? },
            DJUMP(src) => {
                let src_val = self.get_value(src)?;
                expect_value!(src_val, IPtr, InterpreterError::AttemptedJumpToNonIPtr(src_val))?
            },
            BRANCHON(imm, symbol, src) => {
                let val = cookie::BinaryOp::EQ.apply_to(imm, self.get_value(src)?)?;
                let condition = expect_value!(val, Bool, InterpreterError::TypeMismatchError(cookie::Type::Bool, val))?;
                if condition { self.get_target_addr(&symbol)? } else { self.pc + 1 }
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
                    handle.write(s.as_bytes())?;
                    handle.flush()?;
                }
                self.pc + 1
            },
            READ(t, dest) => {
                use self::cookie::Value;
                use self::cookie::Type;

                macro_rules! read_val {
                    ($t:tt) => ({
                        let mut input = String::new();
                        io::stdin().read_line(&mut input)?;
                        input.trim().parse::<$t>()?
                    })
                }

                // macro_rules! read

                let val = match t {
                    Type::I32 => Value::I32(read_val!(i32)),
                    Type::F32 => Value::F32(read_val!(f32)),
                    Type::Bool => Value::Bool(read_val!(bool)),
                    Type::Char => {
                        let mut input = String::new();
                        io::stdin().read_line(&mut input)?;
                        Value::Char(input.chars().nth(0).unwrap())
                    }
                    _ => return Err(InterpreterError::BadInputType(t))
                };
                self.put_value(dest, val)?;
                self.pc + 1
            },
            EXIT => { self.pc = self.instructions.len(); return Ok(Status::Finish); }
        };
        if self.pc < self.instructions.len() { Ok(Status::Ok) } else { Ok(Status::Finish) }
    }

    fn do_pushr(&mut self, reg: cookie::RegisterName) -> Result<()> {
        let val = self.register_get(reg)?;
        self.stack.push(val);
        Ok(())
    }

    fn do_popr(&mut self, reg: cookie::RegisterName) -> Result<()> {
        let val = self.pop()?;
        self.register_put(reg, val)?;
        Ok(())
    }

    fn get_value(&mut self, loc: cookie::Loc) -> Result<cookie::Value> {
        use self::cookie::Loc;
        match loc {
            Loc::Stack => self.pop(),
            Loc::Reg(r) => self.register_get(r),
        }
    }

    fn put_value(&mut self, loc: cookie::Loc, val: cookie::Value) -> Result<()> {
        use self::cookie::Loc;
        match loc {
            Loc::Stack => { self.stack.push(val); Ok(()) },
            Loc::Reg(r) => self.register_put(r, val),
        }
    }

    fn register_get(&mut self, reg: cookie::RegisterName) -> Result<cookie::Value> {
        use self::cookie::Value;
        use self::cookie::RegisterName;
        match reg {
            RegisterName::StackPointer => Ok(Value::SPtr(self.stack.len())),
            RegisterName::FramePointer => Ok(Value::SPtr(self.fp)),
            RegisterName::ProgramCounter => Ok(Value::IPtr(self.pc)),
            _ => Err(InterpreterError::UseOfUnimplementedFeature(format!("Unimplemented register access: {}", reg)))
        }
    }

    fn register_put(&mut self, reg: cookie::RegisterName, val: cookie::Value) -> Result<()> {
        use self::cookie::Value;
        use self::cookie::RegisterName;
        match reg {
            RegisterName::StackPointer => {
                let v = expect_value!(val, SPtr, InterpreterError::TypeMismatchError(cookie::Type::SPtr, val))?;
                self.stack.resize(v, Value::Void);
                Ok(())
            }
            RegisterName::FramePointer => {
                let v = expect_value!(val, SPtr, InterpreterError::TypeMismatchError(cookie::Type::SPtr, val))?;
                self.fp = v;
                Ok(())
            }
            RegisterName::ProgramCounter => {
                self.pc = expect_value!(val, IPtr, InterpreterError::TypeMismatchError(cookie::Type::IPtr, val))?;
                Ok(())
            }
            _ => Err(InterpreterError::UseOfUnimplementedFeature(format!("Unimplemented register access {}", reg)))
        }
    }

    fn pop(&mut self) -> Result<cookie::Value> {
        self.stack.pop().ok_or(InterpreterError::StackUnderflow)
    }

    fn get_target_addr(&self, t: &cookie::Target) -> Result<usize> {
        use cookie_base::Target::*;
        match t {
            &LocalSymbol(addr, _) => Ok(addr),
            &ExternalSymbol(_, ref l) => Err(InterpreterError::UndefinedSymbol(l.to_string())),
            &UnresolvedSymbol(ref l) => Err(InterpreterError::UndefinedSymbol(l.to_string()))
        }
    }
}