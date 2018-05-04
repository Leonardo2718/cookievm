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
pub enum BOp {
    ADD, SUB, MUL, DIV, MOD,
    AND, OR, XOR,
    EQ, LT, LE, GT, GE,
}

impl BOp {
    pub fn apply_to(&self, lhs: Value, rhs: Value) -> Result<Value> {
        let apply_err = Err(format!("Cannot apply {} operation to {} and {}", self, lhs, rhs));
        let apply_err_1 = apply_err.clone();
        let apply_err_2 = apply_err.clone();
        match self {
            BOp::ADD => apply_err
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
            BOp::SUB => apply_err
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
            BOp::MUL => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, *))
                .or_else(apply_binary!(F32, lhs, F32, rhs, F32, *)),
            BOp::DIV => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, /))
                .or_else(apply_binary!(F32, lhs, F32, rhs, F32, /)),
            BOp::MOD => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, %))
                .or_else(apply_binary!(F32, lhs, F32, rhs, F32, %)),

            BOp::EQ => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, Bool, ==))
                .or_else(apply_binary!(F32, lhs, F32, rhs, Bool, ==))
                .or_else(apply_binary!(Char, lhs, Char, rhs, Bool, ==))
                .or_else(apply_binary!(Bool, lhs, Bool, rhs, Bool, ==))
                .or_else(apply_binary!(IPtr, lhs, IPtr, rhs, Bool, ==))
                .or_else(apply_binary!(SPtr, lhs, SPtr, rhs, Bool, ==))
                .or_else(|err: String| match (lhs, rhs) {
                    (Value::Void, Value::Void) => Ok(Value::Bool(true)),
                    _ => Err(err)
                }),
            BOp::LT => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, Bool, <))
                .or_else(apply_binary!(F32, lhs, F32, rhs, Bool, <))
                .or_else(apply_binary!(Char, lhs, Char, rhs, Bool, <)),
            BOp::LE => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, Bool, <=))
                .or_else(apply_binary!(F32, lhs, F32, rhs, Bool, <=))
                .or_else(apply_binary!(Char, lhs, Char, rhs, Bool, <=)),
            BOp::GT => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, Bool, >))
                .or_else(apply_binary!(F32, lhs, F32, rhs, Bool, >))
                .or_else(apply_binary!(Char, lhs, Char, rhs, Bool, >)),
            BOp::GE => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, Bool, >=))
                .or_else(apply_binary!(F32, lhs, F32, rhs, Bool, >=))
                .or_else(apply_binary!(Char, lhs, Char, rhs, Bool, >=)),

            BOp::AND => apply_err
                .or_else(apply_binary!(Bool, lhs, Bool, rhs, Bool, &&))
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, &)),
            BOp::OR => apply_err
                .or_else(apply_binary!(Bool, lhs, Bool, rhs, Bool, ||))
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, |)),
            BOp::XOR => apply_err
                .or_else(apply_binary!(Bool, lhs, Bool, rhs, Bool, !=))
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, ^)),
        }
    }
}

#[derive(Debug,Clone,PartialEq)]
pub enum UOp {
    NEG, NOT
}

impl UOp {
    pub fn apply_to(&self, val: Value) -> Result<Value> {
        let apply_err = Err(format!("Cannot apply {} operation to {}", self, val));
        let apply_err_1 = apply_err.clone();
        let apply_err_2 = apply_err.clone();
        match self {
            UOp::NEG => apply_err
                .or_else(apply_unary!(I32, val, I32, -))
                .or_else(apply_unary!(F32, val, F32, -)),
            UOp::NOT => apply_err
                .or_else(apply_unary!(Bool, val, Bool, !))
                .or_else(apply_unary!(I32, val, I32, !)),
            _ => apply_err
        }
    }
}

impl fmt::Display for BOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl fmt::Display for UOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

// cookie instructions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[derive(Debug,Clone,PartialEq)]
pub enum Instruction {
    PUSHR(RegisterName),
    PUSHC(Value),
    POPR(RegisterName),
    POP,

    STACK_BINARY(BOp),
    STACK_UNARY(UOp),

    JUMP(String),
    JUMPS,
    JUMPO(Value),
    BRANCHEQS(Value, String),
    BRANCHNES(Value, String),

    PRINTS,
    READS(Type),

    HALT,
}

// tests ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[cfg(test)]
mod test {
    use super::*;
    use super::UOp::*;
    use super::BOp::*;

    #[test]
    fn apply_unary_test_1() {
        let val = Value::I32(1);
        assert_eq!(apply_unary!(I32, val, I32, -)("".to_string()).unwrap(), Value::I32(-1));
    }

    #[test]
    fn apply_unary_test_2() {
        let val = Value::F32(3.14159);
        assert_eq!(apply_unary!(F32, val, F32, -)("".to_string()).unwrap(), Value::F32(-3.14159));
    }

    #[test]
    fn apply_unary_test_3() {
        let val = Value::Bool(false);
        assert_eq!(apply_unary!(Bool, val, Bool, !)("".to_string()).unwrap(), Value::Bool(true));
    }

    #[test]
    fn apply_unary_test_5() {
        let val = Value::Char('c');
        assert!(apply_unary!(I32, val, I32, -)("".to_string()).is_err());
    }

    #[test]
    fn apply_unary_test_6() {
        let val = Value::I32(1);
        assert!(apply_unary!(Bool, val, Bool, !)("".to_string()).is_err());
    }

    #[test]
    fn apply_unary_test_7() {
        let val = Value::I32(3);
        assert!(apply_unary!(F32, val, F32, -)("".to_string()).is_err());
    }

    #[test]
    fn apply_binary_test_1() {
        let lhs = Value::I32(1);
        let rhs = Value::I32(2);
        assert_eq!(apply_binary!(I32, lhs, I32, rhs, I32, +)("".to_string()).unwrap(), Value::I32(3));
    }

    #[test]
    fn apply_binary_test_2() {
        let lhs_val = 3.14159;
        let rhs_val = 2.71828;
        let lhs = Value::F32(lhs_val);
        let rhs = Value::F32(rhs_val);
        assert_eq!(apply_binary!(F32, lhs, F32, rhs, F32, -)("".to_string()).unwrap(), Value::F32(lhs_val - rhs_val));
    }

    #[test]
    fn apply_binary_test_3() {
        let lhs = Value::Char('a');
        let rhs = Value::Char('b');
        assert_eq!(apply_binary!(Char, lhs, Char, rhs, Bool, <)("".to_string()).unwrap(), Value::Bool(true));
    }

    #[test]
    fn apply_binary_test_4() {
        let lhs = Value::I32(2);
        let rhs = Value::I32(4);
        assert_eq!(apply_binary!(I32, lhs, I32, rhs, I32, |)("".to_string()).unwrap(), Value::I32(6));
    }

    #[test]
    fn apply_binary_test_5() {
        let lhs = Value::F32(3.14);
        let rhs = Value::F32(3.14);
        assert_eq!(apply_binary!(F32, lhs, F32, rhs, Bool, ==)("".to_string()).unwrap(), Value::Bool(true));
    }

    #[test]
    fn apply_binary_test_6() {
        let lhs = Value::I32(3);
        let rhs = Value::I32(4);
        assert!(apply_binary!(F32, lhs, F32, rhs, F32, +)("".to_string()).is_err());
    }

    #[test]
    fn apply_binary_test_7() {
        let lhs = Value::Bool(true);
        let rhs = Value::Bool(false);
        assert!(apply_binary!(I32, lhs, I32, rhs, I32, &)("".to_string()).is_err());
    }

    #[test]
    fn neg_test_1() {
        let val = Value::I32(3);
        assert_eq!(NEG.apply_to(val).unwrap(), Value::I32(-3));
    }

    #[test]
    fn neg_test_2() {
        let val = Value::F32(-2.71828);
        assert_eq!(NEG.apply_to(val).unwrap(), Value::F32(2.71828));
    }

    #[test]
    fn neg_test_3() {
        let val = Value::Char('x');
        assert!(NEG.apply_to(val).is_err());
    }

    #[test]
    fn neg_test_4() {
        let val = Value::Bool(true);
        assert!(NEG.apply_to(val).is_err());
    }

    #[test]
    fn neg_test_5() {
        let val = Value::IPtr(0x1);
        assert!(NEG.apply_to(val).is_err());
    }

    #[test]
    fn neg_test_6() {
        let val = Value::SPtr(0x1);
        assert!(NEG.apply_to(val).is_err());
    }

    #[test]
    fn neg_test_7() {
        let val = Value::Void;
        assert!(NEG.apply_to(val).is_err());
    }

    #[test]
    fn not_test_1() {
        let val = Value::Bool(true);
        assert_eq!(NOT.apply_to(val).unwrap(), Value::Bool(false));
    }

    #[test]
    fn not_test_2() {
        let val = Value::I32(0xf0f0f0f0);
        assert_eq!(NOT.apply_to(val).unwrap(), Value::I32(0x0f0f0f0f));
    }

    #[test]
    fn not_test_3() {
        let val = Value::F32(3.14159);
        assert!(NOT.apply_to(val).is_err());
    }

    #[test]
    fn not_test_4() {
        let val = Value::Char('z');
        assert!(NOT.apply_to(val).is_err());
    }

    #[test]
    fn not_test_5() {
        let val = Value::IPtr(0xabcd);
        assert!(NOT.apply_to(val).is_err());
    }

    #[test]
    fn not_test_6() {
        let val = Value::SPtr(0xfedc);
        assert!(NOT.apply_to(val).is_err());
    }

    #[test]
    fn not_test_7() {
        let val = Value::Void;
        assert!(NOT.apply_to(val).is_err());
    }

    #[test]
    fn add_test_1() {
        let lhs = Value::I32(1);
        let rhs = Value::I32(2);
        assert_eq!(ADD.apply_to(lhs, rhs).unwrap(), Value::I32(3));
    }

    #[test]
    fn add_test_2() {
        let lhs = Value::F32(1.23);
        let rhs = Value::F32(4.56);
        assert_eq!(ADD.apply_to(lhs, rhs).unwrap(), Value::F32(5.79))
    }

    #[test]
    fn add_test_3() {
        let lhs = Value::IPtr(0x8);
        let rhs = Value::I32(4);
        assert_eq!(ADD.apply_to(lhs, rhs).unwrap(), Value::IPtr(0xc));
    }

    #[test]
    fn add_test_4() {
        let lhs = Value::SPtr(0x8);
        let rhs = Value::I32(4);
        assert_eq!(ADD.apply_to(lhs, rhs).unwrap(), Value::SPtr(0xc));
    }

    #[test]
    fn add_test_5() {
        let lhs = Value::I32(2);
        let rhs = Value::F32(3.0);
        assert!(ADD.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn add_test_6() {
        let lhs = Value::Char('c');
        let rhs = Value::I32(4);
        assert!(ADD.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn add_test_7() {
        let lhs = Value::I32(3);
        let rhs = Value::Bool(true);
        assert!(ADD.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn add_test_8() {
        let lhs = Value::Void;
        let rhs = Value::I32(1);
        assert!(ADD.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn sub_test_1() {
        let lhs = Value::I32(4);
        let rhs = Value::I32(6);
        assert_eq!(SUB.apply_to(lhs, rhs).unwrap(), Value::I32(-2));
    }

    #[test]
    fn sub_test_2() {
        let lhs_val = 3.14159;
        let rhs_val = 2.71828;
        let lhs = Value::F32(lhs_val);
        let rhs = Value::F32(rhs_val);
        assert_eq!(SUB.apply_to(lhs, rhs).unwrap(), Value::F32(lhs_val - rhs_val));
    }

    #[test]
    fn sub_test_3() {
        let lhs = Value::IPtr(0x8);
        let rhs = Value::I32(2);
        assert_eq!(SUB.apply_to(lhs, rhs).unwrap(), Value::IPtr(0x6));
    }

    #[test]
    fn sub_test_4() {
        let lhs = Value::SPtr(0x8);
        let rhs = Value::I32(3);
        assert_eq!(SUB.apply_to(lhs, rhs).unwrap(), Value::SPtr(0x5));
    }

    #[test]
    fn sub_test_5() {
        let lhs = Value::I32(2);
        let rhs = Value::F32(3.0);
        assert!(SUB.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn sub_test_6() {
        let lhs = Value::Char('e');
        let rhs = Value::I32(4);
        assert!(SUB.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn sub_test_7() {
        let lhs = Value::I32(3);
        let rhs = Value::Bool(true);
        assert!(SUB.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn sub_test_8() {
        let lhs = Value::Void;
        let rhs = Value::I32(1);
        assert!(SUB.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn mul_test_1() {
        let lhs = Value::I32(3);
        let rhs = Value::I32(4);
        assert_eq!(MUL.apply_to(lhs,rhs).unwrap(), Value::I32(12));
    }

    #[test]
    fn mul_test_2() {
        let lhs = Value::F32(0.2);
        let rhs = Value::F32(10.0);
        assert_eq!(MUL.apply_to(lhs,rhs).unwrap(), Value::F32(2.0));
    }

    #[test]
    fn mul_test_3() {
        let lhs = Value::F32(2.0);
        let rhs = Value::I32(3);
        assert!(MUL.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn mul_test_4() {
        let lhs = Value::Char('e');
        let rhs = Value::I32(1);
        assert!(MUL.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn mul_test_5() {
        let lhs = Value::F32(1.0);
        let rhs = Value::Bool(true);
        assert!(MUL.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn mul_test_6() {
        let lhs = Value::I32(2);
        let rhs = Value::Void;
        assert!(MUL.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn div_test_1() {
        let lhs = Value::I32(6);
        let rhs = Value::I32(3);
        assert_eq!(DIV.apply_to(lhs,rhs).unwrap(), Value::I32(2));
    }

    #[test]
    fn div_test_2() {
        let lhs = Value::F32(4.68);
        let rhs = Value::F32(2.0);
        assert_eq!(DIV.apply_to(lhs,rhs).unwrap(), Value::F32(2.34));
    }

    #[test]
    fn div_test_3() {
        let lhs = Value::F32(2.0);
        let rhs = Value::I32(10);
        assert!(DIV.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn div_test_4() {
        let lhs = Value::Char('f');
        let rhs = Value::I32(2);
        assert!(DIV.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn div_test_5() {
        let lhs = Value::F32(3.0);
        let rhs = Value::Bool(true);
        assert!(DIV.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn div_test_6() {
        let lhs = Value::I32(5);
        let rhs = Value::Void;
        assert!(DIV.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn mod_test_1() {
        let lhs = Value::I32(5);
        let rhs = Value::I32(3);
        assert_eq!(MOD.apply_to(lhs,rhs).unwrap(), Value::I32(2));
    }

    #[test]
    fn mod_test_2() {
        let lhs_val = 4.68;
        let rhs_val = 1.5;
        let lhs = Value::F32(lhs_val);
        let rhs = Value::F32(rhs_val);
        assert_eq!(MOD.apply_to(lhs,rhs).unwrap(), Value::F32(lhs_val % rhs_val));
    }

    #[test]
    fn mod_test_3() {
        let lhs = Value::F32(2.0);
        let rhs = Value::I32(10);
        assert!(MOD.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn mod_test_4() {
        let lhs = Value::Char('f');
        let rhs = Value::I32(2);
        assert!(MOD.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn mod_test_5() {
        let lhs = Value::F32(3.0);
        let rhs = Value::Bool(true);
        assert!(MOD.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn mod_test_6() {
        let lhs = Value::I32(5);
        let rhs = Value::Void;
        assert!(MOD.apply_to(lhs,rhs).is_err());
    }

    #[test]
    fn eq_test_1() {
        let lhs = Value::I32(4);
        let rhs = Value::I32(4);
        assert_eq!(EQ.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn eq_test_2() {
        let lhs = Value::I32(3);
        let rhs = Value::I32(2);
        assert_eq!(EQ.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn eq_test_3() {
        let lhs = Value::F32(6.47);
        let rhs = Value::F32(6.47);
        assert_eq!(EQ.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn eq_test_4() {
        let lhs = Value::F32(3.14159);
        let rhs = Value::F32(2.71828);
        assert_eq!(EQ.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn eq_test_5() {
        let lhs = Value::Char('c');
        let rhs = Value::Char('c');
        assert_eq!(EQ.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn eq_test_6() {
        let lhs = Value::Char('x');
        let rhs = Value::Char('y');
        assert_eq!(EQ.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn eq_test_7() {
        let lhs = Value::Bool(false);
        let rhs = Value::Bool(false);
        assert_eq!(EQ.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn eq_test_8() {
        let lhs = Value::Bool(false);
        let rhs = Value::Bool(true);
        assert_eq!(EQ.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn eq_test_9() {
        let lhs = Value::IPtr(0x5);
        let rhs = Value::IPtr(0x5);
        assert_eq!(EQ.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn eq_test_10() {
        let lhs = Value::IPtr(0x7);
        let rhs = Value::IPtr(0x4);
        assert_eq!(EQ.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn eq_test_11() {
        let lhs = Value::SPtr(0x5);
        let rhs = Value::SPtr(0x5);
        assert_eq!(EQ.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn eq_test_12() {
        let lhs = Value::SPtr(0x7);
        let rhs = Value::SPtr(0x4);
        assert_eq!(EQ.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn eq_test_13() {
        let lhs = Value::I32(2);
        let rhs = Value::F32(2.0);
        assert!(EQ.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn eq_test_14() {
        let lhs = Value::Char('c');
        let rhs = Value::I32(3);
        assert!(EQ.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn eq_test_15() {
        let lhs = Value::I32(1);
        let rhs = Value::Bool(true);
        assert!(EQ.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn eq_test_16() {
        let lhs = Value::IPtr(0xff);
        let rhs = Value::SPtr(0xff);
        assert!(EQ.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn eq_test_17() {
        let lhs = Value::IPtr(0x3);
        let rhs = Value::I32(3);
        assert!(EQ.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn eq_test_18() {
        let lhs = Value::I32(5);
        let rhs = Value::SPtr(0x5);
        assert!(EQ.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn eq_test_19() {
        let lhs = Value::Void;
        let rhs = Value::I32(0);
        assert!(EQ.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn eq_test_20() {
        let lhs = Value::Char('e');
        let rhs = Value::Void;
        assert!(EQ.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn eq_test_21() {
        let lhs = Value::Void;
        let rhs = Value::Void;
        assert_eq!(EQ.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn lt_test_1() {
        let lhs = Value::I32(3);
        let rhs = Value::I32(4);
        assert_eq!(LT.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn lt_test_2() {
        let lhs = Value::I32(4);
        let rhs = Value::I32(3);
        assert_eq!(LT.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn lt_test_3() {
        let lhs = Value::I32(3);
        let rhs = Value::I32(3);
        assert_eq!(LT.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn lt_test_4() {
        let lhs = Value::F32(3.5);
        let rhs = Value::F32(4.1);
        assert_eq!(LT.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn lt_test_5() {
        let lhs = Value::F32(4.1);
        let rhs = Value::F32(3.5);
        assert_eq!(LT.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn lt_test_6() {
        let lhs = Value::F32(3.5);
        let rhs = Value::F32(3.5);
        assert_eq!(LT.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn lt_test_7() {
        let lhs = Value::Char('d');
        let rhs = Value::Char('e');
        assert_eq!(LT.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn lt_test_8() {
        let lhs = Value::Char('e');
        let rhs = Value::Char('d');
        assert_eq!(LT.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn lt_test_9() {
        let lhs = Value::Char('d');
        let rhs = Value::Char('d');
        assert_eq!(LT.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn lt_test_10() {
        let lhs = Value::Char('a');
        let rhs = Value::I32(1);
        assert!(LT.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn lt_test_11() {
        let lhs = Value::F32(2.0);
        let rhs = Value::I32(1);
        assert!(LT.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn lt_test_12() {
        let lhs = Value::I32(3);
        let rhs = Value::Bool(false);
        assert!(LT.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn lt_test_13() {
        let lhs = Value::Void;
        let rhs = Value::I32(1);
        assert!(LT.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn lt_test_14() {
        let lhs = Value::SPtr(0x2);
        let rhs = Value::I32(1);
        assert!(LT.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn lt_test_15() {
        let lhs = Value::I32(6);
        let rhs = Value::IPtr(0x1);
        assert!(LT.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn lt_test_16() {
        let lhs = Value::Void;
        let rhs = Value::Void;
        assert!(LT.apply_to(lhs, rhs).is_err());
    }


    #[test]
    fn le_test_1() {
        let lhs = Value::I32(3);
        let rhs = Value::I32(4);
        assert_eq!(LE.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn le_test_2() {
        let lhs = Value::I32(4);
        let rhs = Value::I32(3);
        assert_eq!(LE.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn le_test_3() {
        let lhs = Value::I32(3);
        let rhs = Value::I32(3);
        assert_eq!(LE.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn le_test_4() {
        let lhs = Value::F32(3.5);
        let rhs = Value::F32(4.1);
        assert_eq!(LE.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn le_test_5() {
        let lhs = Value::F32(4.1);
        let rhs = Value::F32(3.5);
        assert_eq!(LE.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn le_test_6() {
        let lhs = Value::F32(3.5);
        let rhs = Value::F32(3.5);
        assert_eq!(LE.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn le_test_7() {
        let lhs = Value::Char('d');
        let rhs = Value::Char('e');
        assert_eq!(LE.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn le_test_8() {
        let lhs = Value::Char('e');
        let rhs = Value::Char('d');
        assert_eq!(LE.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn le_test_9() {
        let lhs = Value::Char('d');
        let rhs = Value::Char('d');
        assert_eq!(LE.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn le_test_10() {
        let lhs = Value::Char('a');
        let rhs = Value::I32(1);
        assert!(LE.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn le_test_11() {
        let lhs = Value::F32(2.0);
        let rhs = Value::I32(1);
        assert!(LE.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn le_test_12() {
        let lhs = Value::I32(3);
        let rhs = Value::Bool(false);
        assert!(LE.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn le_test_13() {
        let lhs = Value::Void;
        let rhs = Value::I32(1);
        assert!(LE.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn le_test_14() {
        let lhs = Value::SPtr(0x2);
        let rhs = Value::I32(1);
        assert!(LE.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn le_test_15() {
        let lhs = Value::I32(6);
        let rhs = Value::IPtr(0x1);
        assert!(LE.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn le_test_16() {
        let lhs = Value::Void;
        let rhs = Value::Void;
        assert!(LE.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn gt_test_1() {
        let lhs = Value::I32(3);
        let rhs = Value::I32(4);
        assert_eq!(GT.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn gt_test_2() {
        let lhs = Value::I32(4);
        let rhs = Value::I32(3);
        assert_eq!(GT.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn gt_test_3() {
        let lhs = Value::I32(3);
        let rhs = Value::I32(3);
        assert_eq!(GT.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn gt_test_4() {
        let lhs = Value::F32(3.5);
        let rhs = Value::F32(4.1);
        assert_eq!(GT.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn gt_test_5() {
        let lhs = Value::F32(4.1);
        let rhs = Value::F32(3.5);
        assert_eq!(GT.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn gt_test_6() {
        let lhs = Value::F32(3.5);
        let rhs = Value::F32(3.5);
        assert_eq!(GT.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn gt_test_7() {
        let lhs = Value::Char('d');
        let rhs = Value::Char('e');
        assert_eq!(GT.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn gt_test_8() {
        let lhs = Value::Char('e');
        let rhs = Value::Char('d');
        assert_eq!(GT.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn gt_test_9() {
        let lhs = Value::Char('d');
        let rhs = Value::Char('d');
        assert_eq!(GT.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn gt_test_10() {
        let lhs = Value::Char('a');
        let rhs = Value::I32(1);
        assert!(GT.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn gt_test_11() {
        let lhs = Value::F32(2.0);
        let rhs = Value::I32(1);
        assert!(GT.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn gt_test_12() {
        let lhs = Value::I32(3);
        let rhs = Value::Bool(false);
        assert!(GT.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn gt_test_13() {
        let lhs = Value::Void;
        let rhs = Value::I32(1);
        assert!(GT.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn gt_test_14() {
        let lhs = Value::SPtr(0x2);
        let rhs = Value::I32(1);
        assert!(GT.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn gt_test_15() {
        let lhs = Value::I32(6);
        let rhs = Value::IPtr(0x1);
        assert!(GT.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn gt_test_16() {
        let lhs = Value::Void;
        let rhs = Value::Void;
        assert!(GT.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn ge_test_1() {
        let lhs = Value::I32(3);
        let rhs = Value::I32(4);
        assert_eq!(GE.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn ge_test_2() {
        let lhs = Value::I32(4);
        let rhs = Value::I32(3);
        assert_eq!(GE.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn ge_test_3() {
        let lhs = Value::I32(3);
        let rhs = Value::I32(3);
        assert_eq!(GE.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn ge_test_4() {
        let lhs = Value::F32(3.5);
        let rhs = Value::F32(4.1);
        assert_eq!(GE.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn ge_test_5() {
        let lhs = Value::F32(4.1);
        let rhs = Value::F32(3.5);
        assert_eq!(GE.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn ge_test_6() {
        let lhs = Value::F32(3.5);
        let rhs = Value::F32(3.5);
        assert_eq!(GE.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn ge_test_7() {
        let lhs = Value::Char('d');
        let rhs = Value::Char('e');
        assert_eq!(GE.apply_to(lhs, rhs).unwrap(), Value::Bool(false));
    }

    #[test]
    fn ge_test_8() {
        let lhs = Value::Char('e');
        let rhs = Value::Char('d');
        assert_eq!(GE.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn ge_test_9() {
        let lhs = Value::Char('d');
        let rhs = Value::Char('d');
        assert_eq!(GE.apply_to(lhs, rhs).unwrap(), Value::Bool(true));
    }

    #[test]
    fn ge_test_10() {
        let lhs = Value::Char('a');
        let rhs = Value::I32(1);
        assert!(GE.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn ge_test_11() {
        let lhs = Value::F32(2.0);
        let rhs = Value::I32(1);
        assert!(GE.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn ge_test_12() {
        let lhs = Value::I32(3);
        let rhs = Value::Bool(false);
        assert!(GE.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn ge_test_13() {
        let lhs = Value::Void;
        let rhs = Value::I32(1);
        assert!(GE.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn ge_test_14() {
        let lhs = Value::SPtr(0x2);
        let rhs = Value::I32(1);
        assert!(GE.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn ge_test_15() {
        let lhs = Value::I32(6);
        let rhs = Value::IPtr(0x1);
        assert!(GE.apply_to(lhs, rhs).is_err());
    }

    #[test]
    fn ge_test_16() {
        let lhs = Value::Void;
        let rhs = Value::Void;
        assert!(GE.apply_to(lhs, rhs).is_err());
    }

}
