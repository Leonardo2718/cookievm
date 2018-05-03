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
use std::fmt;
use std::result;

type Result<T> = result::Result<T, String>;

// cookie data types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[derive(Debug,Clone,Copy,PartialEq)]
pub enum Type {
    I32,
    F32,
    Char,
    Bool,
    IPtr,
    SPtr,
    Void,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

// cookie values ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[derive(Debug,Clone,Copy,PartialEq)]
pub enum Value {
    I32(i32),
    F32(f32),
    Char(char),
    Bool(bool),
    IPtr(usize),
    SPtr(usize),
    Void,
}

impl Value {
    pub fn get_type(&self) -> Type {
        match self {
            Value::I32(_) => Type::I32,
            Value::F32(_) => Type::F32,
            Value::Char(_) => Type::Char,
            Value::Bool(_) => Type::Bool,
            Value::IPtr(_) => Type::IPtr,
            Value::SPtr(_) => Type::SPtr,
            Value::Void => Type::Void,
        }
    }

    pub fn is_type(&self, t: Type) -> bool { t == self.get_type() }

    pub fn value_as_str(&self) -> String {
        use self::Value::*;
        match self {
            I32(i) => i.to_string(),
            F32(f) => f.to_string(),
            Char(c) => c.to_string(),
            Bool(b) => b.to_string(),
            _ => self.to_string(),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Value::*;
        match self {
            IPtr(a) => write!(f, "IPtr(0x{:x})", a),
            SPtr(a) => write!(f, "SPtr(0x{:x})", a),
            v => write!(f, "{:?}", v)
        }
    }
}

macro_rules! apply_binary {
    ($lmatch:ident, $lhs:expr, $rmatch:ident, $rhs:expr, $res:ident, $op:tt) => (
        |err: String| match ($lhs, $rhs) {
            (Value::$lmatch(l), Value::$rmatch(r)) => Ok(Value::$res(l.clone() $op r.clone())),
            _ => Err(err)
        }
    )
}

macro_rules! apply_unary {
    ($matcher:ident, $expr:expr, $res:ident, $op:tt) => {
        |err: String| match $expr {
            Value::$matcher(val) => Ok(Value::$res($op(val.clone()))),
            _ => Err(err)
        }
    }
}

// cookie register names ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[derive(Debug,Clone,Copy,PartialEq)]
pub enum RegisterName {
    StackPointer,
    FramePointer,
    ProgramCounter,
    R(u8),
}

impl fmt::Display for RegisterName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            RegisterName::R(i) => write!(f, "R{}", i),
            r => write!(f, "{:?}", r)
        }
    }
}

// cookie operations ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[derive(Debug,Clone,PartialEq)]
pub enum BinaryOperation {
    ADD, SUB, MUL, DIV, MOD,
    AND, OR, XOR,
    EQ, LT, LE, GT, GE,
}

fn map_i32<F>(lhs: Value, rhs: Value, f: F) -> impl Fn(String) -> Result<Value>
where F: Fn(i32, i32) -> Value {
    move |err| match (&lhs, &rhs) {
        (Value::I32(l), Value::I32(r)) => Ok(f(l.clone(), r.clone())),
        _ => Err(err)
    }
}

impl BinaryOperation {
    pub fn apply(&self, lhs: Value, rhs: Value) -> Result<Value> {
        let apply_err = Err(format!("Cannot apply {} operation to {} and {}", self, lhs, rhs));
        let apply_err_1 = apply_err.clone();
        let apply_err_2 = apply_err.clone();
        match self {
            BinaryOperation::ADD => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, +))
                .or_else(apply_binary!(F32, lhs, F32, rhs, F32, +))
                .or_else(apply_binary!(
                    IPtr, lhs,
                    IPtr,
                    apply_err_1.or_else(apply_unary!(I32, rhs, IPtr, (|i| i as usize)))?,
                    IPtr, +))
                .or_else(apply_binary!(
                    SPtr, lhs,
                    SPtr,
                    apply_err_2.or_else(apply_unary!(I32, rhs, SPtr, (|i| i as usize)))?,
                    SPtr, +)),
            BinaryOperation::SUB => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, -))
                .or_else(apply_binary!(F32, lhs, F32, rhs, F32, -))
                .or_else(apply_binary!(
                    IPtr, lhs,
                    IPtr,
                    apply_err_1.or_else(apply_unary!(I32, rhs, IPtr, (|i| i as usize)))?,
                    IPtr, -))
                .or_else(apply_binary!(
                    SPtr, lhs,
                    SPtr,
                    apply_err_2.or_else(apply_unary!(I32, rhs, SPtr, (|i| i as usize)))?,
                    SPtr, -)),
            BinaryOperation::MUL => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, *))
                .or_else(apply_binary!(F32, lhs, F32, rhs, F32, *)),
            BinaryOperation::DIV => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, /))
                .or_else(apply_binary!(F32, lhs, F32, rhs, F32, /)),
            BinaryOperation::MOD => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, %))
                .or_else(apply_binary!(F32, lhs, F32, rhs, F32, %)),

            BinaryOperation::EQ => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, Bool, ==))
                .or_else(apply_binary!(F32, lhs, F32, rhs, Bool, ==))
                .or_else(apply_binary!(IPtr, lhs, IPtr, rhs, Bool, ==))
                .or_else(apply_binary!(SPtr, lhs, SPtr, rhs, Bool, ==)),
            BinaryOperation::LT => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, Bool, <))
                .or_else(apply_binary!(F32, lhs, F32, rhs, Bool, <)),
            BinaryOperation::LE => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, Bool, <=))
                .or_else(apply_binary!(F32, lhs, F32, rhs, Bool, <=)),
            BinaryOperation::GT => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, Bool, >))
                .or_else(apply_binary!(F32, lhs, F32, rhs, Bool, >)),
            BinaryOperation::GE => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, Bool, >=))
                .or_else(apply_binary!(F32, lhs, F32, rhs, Bool, >=)),

            BinaryOperation::AND => apply_err
                .or_else(apply_binary!(Bool, lhs, Bool, rhs, Bool, &&))
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, &)),
            BinaryOperation::OR => apply_err
                .or_else(apply_binary!(Bool, lhs, Bool, rhs, Bool, ||))
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, |)),
            BinaryOperation::XOR => apply_err
                .or_else(apply_binary!(Bool, lhs, Bool, rhs, Bool, !=))
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, ^)),
        }
    }
}

#[derive(Debug,Clone,PartialEq)]
pub enum UnaryOperation {
    NEG, NOT
}

impl UnaryOperation {
    pub fn apply(&self, val: Value) -> Result<Value> {
        let apply_err = Err(format!("Cannot apply {} operation to {}", self, val));
        let apply_err_1 = apply_err.clone();
        let apply_err_2 = apply_err.clone();
        match self {
            UnaryOperation::NEG => apply_err
                .or_else(apply_unary!(I32, val, I32, -))
                .or_else(apply_unary!(F32, val, F32, -)),
            UnaryOperation::NOT => apply_err
                .or_else(apply_unary!(Bool, val, Bool, !))
                .or_else(apply_unary!(I32, val, I32, !)),
        }
    }
}

impl fmt::Display for BinaryOperation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Display for UnaryOperation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

// cookie instructions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[derive(Debug,Clone,PartialEq)]
pub enum Instruction {
    PUSHR(RegisterName),
    PUSHC(Value),
    POPR(RegisterName),
    POP,

    STACK_BINARY(BinaryOperation),
    STACK_UNARY(UnaryOperation),

    JUMP(String),
    JUMPS,
    JUMPO(Value),
    BRANCHEQS(Value, String),
    BRANCHNES(Value, String),

    PRINTS,
    READS(Type),

    HALT,
}
