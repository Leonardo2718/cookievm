/*

Copyright (C) 2018, 2020 Leonardo Banderali

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

use instruction as cookie;
use std::convert;
use std::error;
use std::fmt;
use std::io;
use std::io::Write;
use std::num;
use std::result;
use std::str;

#[derive(Debug)]
pub enum InterpreterError {
    AttemptedLoadFromNonSPtr(cookie::Value),
    AttemptedJumpToNonIPtr(cookie::Value),
    TypeMismatchError(cookie::Type, cookie::Value),
    UseOfNullPtr,
    BadInputType(cookie::Type),
    BadSource(cookie::Source),
    BadSourceCombination(cookie::Source, cookie::Source),
    Bad3SourceCombination(cookie::Source, cookie::Source, cookie::Source),
    BadDestination(cookie::Destination),
    StackUnderflow,
    StackOverflow,
    UndefinedSymbol(String),
    OutOfRangeInstruction(usize),
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
            &AttemptedLoadFromNonSPtr(_) => {
                "Attempted to load value from non-SPtr (non stack address)"
            }
            &AttemptedJumpToNonIPtr(_) => "Attempted to jump to non-IPtr (non instruction address)",
            &TypeMismatchError(_, _) => "Got value of unexpected type",
            &UseOfNullPtr => "Attempted to dereference a null pointer",
            &BadInputType(_) => "Cannot read input of given type",
            &BadSource(_) => "Specified source operand is invalid",
            &BadSourceCombination(_, _) => "Specified source operands are invalid",
            &Bad3SourceCombination(_, _, _) => "Specified source operands are invalid",
            &BadDestination(_) => "Specified result destination is invalid",
            &StackUnderflow => "Attempted to pop value but stack is empty",
            &StackOverflow => "Attempted to push value but stack is full",
            &UndefinedSymbol(_) => "Attempted to reference a symbol that does not exist",
            &OutOfRangeInstruction(_) => {
                "Attempted to execute instruction at address past the end of instruction sequence"
            }
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
            _ => None,
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
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Status {
    Ok,     // default normal
    Finish, // normal program termination
}

macro_rules! expect_value {
    ($expr:expr, $ctor:ident, $err:expr) => {
        match $expr {
            cookie::Value::$ctor(v) => Ok(v),
            _v => Err($err),
        }
    };
}

macro_rules! null_check {
    ($val:expr) => {
        if $val == 0 {
            return Err(InterpreterError::UseOfNullPtr);
        }
    };
}

impl Interpreter {
    pub fn new(instructions: cookie::InstructionList) -> Interpreter {
        Interpreter {
            instructions,
            stack: Vec::with_capacity(100),
            fp: 0,
            pc: 0,
            gpr: [cookie::Value::Void; 16],
        }
    }

    pub fn exec_next(&mut self) -> Result<Status> {
        let inst = self.get_next()?.clone();
        self.exec_instruction(inst)
    }

    fn get_next(&self) -> Result<&cookie::Instruction> {
        self.instructions
            .get(self.pc)
            .ok_or(InterpreterError::OutOfRangeInstruction(self.pc))
    }

    pub fn exec_instruction(&mut self, inst: cookie::Instruction) -> Result<Status> {
        use instruction::Instruction::*;
        self.pc = match inst {
            PUSHR(reg) => {
                self.do_pushr(reg)?;
                self.pc + 1
            }
            PUSHC(v) => {
                self.stack.push(v.clone());
                self.pc + 1
            }
            POPR(reg) => {
                self.do_popr(reg)?;
                self.pc + 1
            }
            POP => {
                self.pop()?;
                self.pc + 1
            }
            MOVE(dest, src) => {
                let val = self.get_value(src)?;
                self.put_value(dest, val)?;
                self.pc + 1
            }
            LOADFROM(dest, src) => {
                let src_val = self.get_value(src)?;
                let addr = expect_value!(
                    src_val,
                    SPtr,
                    InterpreterError::AttemptedLoadFromNonSPtr(src_val)
                )?;
                null_check!(addr);
                let val = self.stack[addr - 1];
                self.put_value(dest, val)?;
                self.pc + 1
            }
            STORETO(src, dest) => {
                let (val, dest_val) = self.get2_values(dest, src)?;
                let addr = expect_value!(
                    dest_val,
                    SPtr,
                    InterpreterError::AttemptedLoadFromNonSPtr(dest_val)
                )?;
                null_check!(addr);
                self.stack[addr - 1] = val;
                self.pc + 1
            }
            UOp(op, dest, src) => {
                let val = self.get_value(src)?;
                let res = op.apply_to(val)?;
                self.put_value(dest, res)?;
                self.pc + 1
            }
            BOp(op, dest, lhs, rhs) => {
                let (lhs_v, rhs_v) = self.get2_values(lhs, rhs)?;
                let res = op.apply_to(lhs_v, rhs_v)?;
                self.put_value(dest, res)?;
                self.pc + 1
            }
            JUMP(symbol) => self.get_target_addr(&symbol)?,
            DJUMP(src) => {
                let src_val = self.get_value(src)?;
                expect_value!(
                    src_val,
                    IPtr,
                    InterpreterError::AttemptedJumpToNonIPtr(src_val)
                )?
            }
            BRANCH(src, symbol) => {
                let val = self.get_value(src)?;
                let condition = expect_value!(
                    val,
                    Bool,
                    InterpreterError::TypeMismatchError(cookie::Type::Bool, val)
                )?;
                if condition {
                    self.get_target_addr(&symbol)?
                } else {
                    self.pc + 1
                }
            }
            DBRANCH(src1, src2) => {
                let (val1, val2) = self.get2_values(src1, src2)?;
                let condition = expect_value!(
                    val1,
                    Bool,
                    InterpreterError::TypeMismatchError(cookie::Type::Bool, val1)
                )?;
                if condition {
                    expect_value!(val2, IPtr, InterpreterError::AttemptedJumpToNonIPtr(val2))?
                } else {
                    self.pc + 1
                }
            }
            PRINT(src) => {
                use self::cookie::Value::*;
                let s = match self.get_value(src)? {
                    Char(c) => format!("{}", c),
                    I32(i) => format!("{}", i),
                    F32(f) => format!("{}", f),
                    Bool(b) => format!("{}", b),
                    v => format!("{}", v),
                };
                {
                    let stdout = io::stdout();
                    let mut handle = stdout.lock();
                    handle.write(s.as_bytes())?;
                    handle.flush()?;
                }
                self.pc + 1
            }
            READ(t, dest) => {
                use self::cookie::Type;
                use self::cookie::Value;

                macro_rules! read_val {
                    ($t:tt) => {{
                        let mut input = String::new();
                        io::stdin().read_line(&mut input)?;
                        input.trim().parse::<$t>()?
                    }};
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
                    _ => return Err(InterpreterError::BadInputType(t)),
                };
                self.put_value(dest, val)?;
                self.pc + 1
            }
            EXIT => {
                self.pc = self.instructions.len();
                return Ok(Status::Finish);
            }
        };
        if self.pc < self.instructions.len() {
            Ok(Status::Ok)
        } else {
            Ok(Status::Finish)
        }
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

    fn get3_values(
        &mut self,
        src1: cookie::Source,
        src2: cookie::Source,
        src3: cookie::Source,
    ) -> Result<(cookie::Value, cookie::Value, cookie::Value)> {
        use self::cookie::Source::*;
        let v3 = self.get_value(src3)?;
        let v2 = self.get_value(src2)?;
        let v1 = self.get_value(src1)?;
        Ok((v1, v2, v3))
    }

    fn get2_values(
        &mut self,
        srcl: cookie::Source,
        srcr: cookie::Source,
    ) -> Result<(cookie::Value, cookie::Value)> {
        use self::cookie::Source::*;
        let r = self.get_value(srcr)?;
        let l = self.get_value(srcl)?;
        Ok((l, r))
    }

    fn get_value(&mut self, src: cookie::Source) -> Result<cookie::Value> {
        use self::cookie::Source::*;
        match src {
            Register(r) => self.register_get(r),
            Immediate(v) => Ok(v),
            Stack => self.pop(),
            _ => Err(InterpreterError::BadSource(src)),
        }
    }

    fn put_value(&mut self, dest: cookie::Destination, val: cookie::Value) -> Result<()> {
        use self::cookie::Destination::*;
        match dest {
            Register(r) => self.register_put(r, val),
            Stack => {
                self.stack.push(val);
                Ok(())
            }
            _ => Err(InterpreterError::BadDestination(dest)),
        }
    }

    fn register_get(&mut self, reg: cookie::RegisterName) -> Result<cookie::Value> {
        use self::cookie::RegisterName;
        use self::cookie::Value;
        match reg {
            RegisterName::StackPointer => Ok(Value::SPtr(self.stack.len())),
            RegisterName::FramePointer => Ok(Value::SPtr(self.fp)),
            RegisterName::ProgramCounter => Ok(Value::IPtr(self.pc)),
            RegisterName::R(x) => Ok(self.gpr[x as usize].clone()),
        }
    }

    fn register_put(&mut self, reg: cookie::RegisterName, val: cookie::Value) -> Result<()> {
        use self::cookie::RegisterName;
        use self::cookie::Value;
        match reg {
            RegisterName::StackPointer => {
                let v = expect_value!(
                    val,
                    SPtr,
                    InterpreterError::TypeMismatchError(cookie::Type::SPtr, val)
                )?;
                self.stack.resize(v, Value::Void);
                Ok(())
            }
            RegisterName::FramePointer => {
                let v = expect_value!(
                    val,
                    SPtr,
                    InterpreterError::TypeMismatchError(cookie::Type::SPtr, val)
                )?;
                self.fp = v;
                Ok(())
            }
            RegisterName::ProgramCounter => {
                self.pc = expect_value!(
                    val,
                    IPtr,
                    InterpreterError::TypeMismatchError(cookie::Type::IPtr, val)
                )?;
                Ok(())
            }
            RegisterName::R(x) => {
                self.gpr[x as usize] = val;
                Ok(())
            }
        }
    }

    fn pop(&mut self) -> Result<cookie::Value> {
        self.stack.pop().ok_or(InterpreterError::StackUnderflow)
    }

    fn get_target_addr(&self, t: &cookie::Target) -> Result<usize> {
        use instruction::Target::*;
        match t {
            &LocalSymbol(addr, _) => Ok(addr),
            &ExternalSymbol(_, ref l) => Err(InterpreterError::UndefinedSymbol(l.to_string())),
            &UnresolvedSymbol(ref l) => Err(InterpreterError::UndefinedSymbol(l.to_string())),
        }
    }
}
