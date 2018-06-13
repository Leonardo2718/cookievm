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
use std::error;
use std::convert;

// pub type Result<T> = result::Result<T, String>;

// cookie data types and value ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

macro_rules! define_types {
    [$( ($n:ident,$t:ty) ),+] => {
        #[derive(Debug,Clone,Copy,PartialEq)]
        pub enum Type { $($n),+ , Void }

        pub mod RustType {
            $( pub type $n = $t );+;
            pub type Void = ();
        }
        
        #[derive(Debug,Clone,Copy,PartialEq)]
        pub enum Value { $($n($t)),+ , Void }

        impl Value {
            pub fn get_type(&self) -> Type {
                match self {
                    $( Value::$n(_) => Type::$n ),+ ,
                    Value::Void => Type::Void
                }
            }
        }
    }
}

define_types![ (I32, i32)
             , (F32, f32)
             , (Char, char)
             , (Bool, bool)
             , (IPtr, usize)
             , (SPtr, usize)
             ];

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
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

#[derive(Debug,Clone,PartialEq)]
pub struct ConversionError(Value, Type);

impl Value {
    pub fn is_type(&self, t: Type) -> bool { t == self.get_type() }

    pub fn convert_to(&self, t: Type) -> result::Result<Value, ConversionError> {
        if self.is_type(t) { return Ok(*self); }

        macro_rules! cast {
            (I32, Bool; $v:expr) => { $v != 0 };
            (F32, Bool; $v:expr) => { $v != 0.0 };
            (Char, Bool; $v:expr) => { $v != '\0' };
            (IPtr, Bool; $v:expr) => { $v != 0 };
            (SPtr, Bool; $v:expr) => { $v != 0 };
            ($S:ident, $D:ident; $v:expr) => { $v as RustType::$D };
        }

        macro_rules! allowed_cvt {
            [ $($src:ident -> $dest:ident),+ ] => {
                match (self, t) {
                    $( (&Value::$src(v), Type::$dest) => Ok(Value::$dest( cast!($src,$dest;v) )) ),+ ,
                    _ => Err(ConversionError(*self,t))
                }
            };
        }

        return allowed_cvt! [ F32 -> I32
                            , Char -> I32
                            , Bool -> I32
                            , IPtr -> I32
                            , SPtr -> I32
                            , I32 -> F32
                            // , I32 -> Char
                            , I32 -> Bool
                            , F32 -> Bool
                            , Char -> Bool
                            , IPtr -> Bool
                            , SPtr -> Bool
                            , I32 -> IPtr
                            , I32 -> SPtr
                            ];
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
pub enum OpApplicationError {
    BadBinaryOp(BinaryOp,Value,Value),
    BadUnaryOp(UnaryOp,Value),
    BadConversion(ConversionError),
}

impl fmt::Display for OpApplicationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl error::Error for OpApplicationError {
    fn description(&self) -> &str {
        use self::OpApplicationError::*;
        match self {
            &BadBinaryOp(_,_,_) => "Cannot apply binary operation to given values (cannot operate on given types)",
            &BadUnaryOp(_,_) => "Cannot apply unary operation to given value (unsupported type)",
            &BadConversion(_) => "Cannot convert source value to target type",
        }
    }

    fn cause(&self) -> Option<&error::Error> {
        None
    }
}

impl convert::From<ConversionError> for OpApplicationError {
    fn from(error: ConversionError) -> Self {
        OpApplicationError::BadConversion(error)
    }
}

#[derive(Debug,Clone,PartialEq)]
pub enum UnaryOp {
    NEG, NOT, CVT(Type)
}
// macro_rules! apply_unary {
//     ($matcher:ident, $expr:expr, $res:ident, $op:tt) => {
//         |err: String| match $expr {
//             Value::$matcher(val) => Ok(Value::$res($op(val.clone()))),
//             _ => Err(err)
//         }
//     }
// }

impl UnaryOp {
    pub fn apply_to(&self, val: Value) -> result::Result<Value,OpApplicationError> {
        let apply_err = OpApplicationError::BadUnaryOp(self.clone(),val);

        // macro_rules! allow_cvt {
        //     ($src:ident,$dest:ident) => {
        //         Value::$src(v) => Value::$dest
        //     }
        // }

        let v = match self {
            UnaryOp::NEG => match val {
                Value::I32(v) => Value::I32(-v),
                Value::F32(v) => Value::F32(-v),
                _ => return Err(apply_err),
            }   //apply_err
                // .or_else(apply_unary!(I32, val, I32, -))
                // .or_else(apply_unary!(F32, val, F32, -)),
            UnaryOp::NOT => match val {
                Value::Bool(v) => Value::Bool(!v),
                Value::I32(v) => Value::I32(!v),
                _ => return Err(apply_err),
            }
                // apply_err
                // .or_else(apply_unary!(Bool, val, Bool, !))
                // .or_else(apply_unary!(I32, val, I32, !)),
            UnaryOp::CVT(t) => val.convert_to(*t)?
            // UnaryOp::CVT(Type::I32) => val.convert_to(Type::I32)?,
            //     // cvt_err!(Type::I32)
            //     // .or_else(apply_unary!(I32, val, I32, (|v| v)))
            //     // .or_else(apply_unary!(F32, val, I32, (|v| v as i32)))
            //     // .or_else(apply_unary!(Char, val, I32, (|v| v as i32)))
            //     // .or_else(apply_unary!(Bool, val, I32, (|v| v as i32)))
            //     // .or_else(apply_unary!(IPtr, val, I32, (|v| v as i32)))
            //     // .or_else(apply_unary!(SPtr, val, I32, (|v| v as i32))),
            // UnaryOp::CVT(Type::F32) => val.convert_to(Type::F32)?,
            //     // cvt_err!(Type::F32)
            //     // .or_else(apply_unary!(I32, val, F32, (|v| v as f32)))
            //     // .or_else(apply_unary!(F32, val, F32, (|v| v))),
            // UnaryOp::CVT(Type::Char) => val.convert_to(Type::Char)?,
            //     // cvt_err!(Type::Char)
            //     // .or_else(apply_unary!(Char, val, Char, (|v| v))),
            // UnaryOp::CVT(Type::Bool) => val.convert_to(Type::Bool)?,
            //     // cvt_err!(Type::Bool)
            //     // .or_else(apply_unary!(I32, val, Bool, (|v| v != 0)))
            //     // .or_else(apply_unary!(F32, val, Bool, (|v| v != 0.0)))
            //     // .or_else(apply_unary!(Char, val, Bool, (|v| v != '\0')))
            //     // .or_else(apply_unary!(Bool, val, Bool, (|v| v)))
            //     // .or_else(apply_unary!(IPtr, val, Bool, (|v| v != 0)))
            //     // .or_else(apply_unary!(SPtr, val, Bool, (|v| v != 0))),
            // UnaryOp::CVT(Type::IPtr) => val.convert_to(Type::IPtr)?,
            //     // cvt_err!(Type::IPtr)
            //     // .or_else(apply_unary!(I32, val, IPtr, (|v| v as usize)))
            //     // .or_else(apply_unary!(IPtr, val, IPtr, (|v| v as usize))),
            // UnaryOp::CVT(Type::SPtr) => val.convert_to(Type::SPtr)?,
            //     // cvt_err!(Type::IPtr)
            //     // .or_else(apply_unary!(I32, val, SPtr, (|v| v as usize)))
            //     // .or_else(apply_unary!(SPtr, val, SPtr, (|v| v as usize))),
            // UnaryOp::CVT(Type::Void) => val.convert_to(Type::Void)?//cvt_err!(Type::Void)
        };

        return Ok(v);
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug,Clone,PartialEq)]
pub enum BinaryOp {
    ADD, SUB, MUL, DIV, MOD,
    AND, OR, XOR,
    EQ, LT, LE, GT, GE,
}

macro_rules! apply_binary {
    ($lmatch:ident, $lhs:expr, $rmatch:ident, $rhs:expr, $res:ident, $op:tt) => (
        |err: OpApplicationError| match ($lhs, $rhs) {
            (Value::$lmatch(l), Value::$rmatch(r)) => Ok(Value::$res(l.clone() $op r.clone())),
            _ => Err(err)
        }
    )
}

macro_rules! apply_binaryf {
    ($lmatch:ident, $lhs:expr, $rmatch:ident, $rhs:expr, $res:ident, $op:tt) => (
        |err: OpApplicationError| match ($lhs, $rhs) {
            (Value::$lmatch(l), Value::$rmatch(r)) => Ok(Value::$res($op(l.clone(), r.clone()))),
            _ => Err(err)
        }
    )
}

fn ptr_add(lhs: usize, rhs:i32) -> usize {
    if rhs < 0 { lhs - (-rhs as usize) }
    else { lhs + rhs as usize }
}

fn ptr_sub(lhs: usize, rhs:i32) -> usize {
    if rhs < 0 { lhs + (-rhs as usize) }
    else { lhs - rhs as usize }
}

impl BinaryOp {
    pub fn apply_to(&self, lhs: Value, rhs: Value) -> result::Result<Value, OpApplicationError> {
        let apply_err = Err(OpApplicationError::BadBinaryOp(self.clone(), lhs, rhs));
        match self {
            BinaryOp::ADD => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, +))
                .or_else(apply_binary!(F32, lhs, F32, rhs, F32, +))
                .or_else(apply_binaryf!(
                    IPtr, lhs,
                    I32, rhs,
                    IPtr, ptr_add))
                .or_else(apply_binaryf!(
                    SPtr, lhs,
                    I32, rhs,
                    SPtr, ptr_add)),
            BinaryOp::SUB => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, -))
                .or_else(apply_binary!(F32, lhs, F32, rhs, F32, -))
                .or_else(apply_binaryf!(
                    IPtr, lhs,
                    I32, rhs,
                    IPtr, ptr_sub))
                .or_else(apply_binaryf!(
                    SPtr, lhs,
                    I32, rhs,
                    SPtr, ptr_sub)),
            BinaryOp::MUL => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, *))
                .or_else(apply_binary!(F32, lhs, F32, rhs, F32, *)),
            BinaryOp::DIV => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, /))
                .or_else(apply_binary!(F32, lhs, F32, rhs, F32, /)),
            BinaryOp::MOD => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, %))
                .or_else(apply_binary!(F32, lhs, F32, rhs, F32, %)),

            BinaryOp::EQ => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, Bool, ==))
                .or_else(apply_binary!(F32, lhs, F32, rhs, Bool, ==))
                .or_else(apply_binary!(Char, lhs, Char, rhs, Bool, ==))
                .or_else(apply_binary!(Bool, lhs, Bool, rhs, Bool, ==))
                .or_else(apply_binary!(IPtr, lhs, IPtr, rhs, Bool, ==))
                .or_else(apply_binary!(SPtr, lhs, SPtr, rhs, Bool, ==))
                .or_else(|err: OpApplicationError| match (lhs, rhs) {
                    (Value::Void, Value::Void) => Ok(Value::Bool(true)),
                    _ => Err(err)
                }),
            BinaryOp::LT => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, Bool, <))
                .or_else(apply_binary!(F32, lhs, F32, rhs, Bool, <))
                .or_else(apply_binary!(Char, lhs, Char, rhs, Bool, <)),
            BinaryOp::LE => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, Bool, <=))
                .or_else(apply_binary!(F32, lhs, F32, rhs, Bool, <=))
                .or_else(apply_binary!(Char, lhs, Char, rhs, Bool, <=)),
            BinaryOp::GT => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, Bool, >))
                .or_else(apply_binary!(F32, lhs, F32, rhs, Bool, >))
                .or_else(apply_binary!(Char, lhs, Char, rhs, Bool, >)),
            BinaryOp::GE => apply_err
                .or_else(apply_binary!(I32, lhs, I32, rhs, Bool, >=))
                .or_else(apply_binary!(F32, lhs, F32, rhs, Bool, >=))
                .or_else(apply_binary!(Char, lhs, Char, rhs, Bool, >=)),

            BinaryOp::AND => apply_err
                .or_else(apply_binary!(Bool, lhs, Bool, rhs, Bool, &&))
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, &)),
            BinaryOp::OR => apply_err
                .or_else(apply_binary!(Bool, lhs, Bool, rhs, Bool, ||))
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, |)),
            BinaryOp::XOR => apply_err
                .or_else(apply_binary!(Bool, lhs, Bool, rhs, Bool, !=))
                .or_else(apply_binary!(I32, lhs, I32, rhs, I32, ^)),
        }
    }
}

// cookie instructions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[derive(Debug,Clone,Copy,PartialEq)]
pub enum Loc {
    Stack,
    Reg(RegisterName),
}

#[derive(Debug,Clone,PartialEq)]
pub enum Instruction {
    PUSHR(RegisterName),
    PUSHC(Value),
    POPR(RegisterName),
    POP,

    LOADFROM(Loc, Loc),
    STORETO(Loc, Loc),

    UOp(UnaryOp, Loc, Loc),
    BOp(BinaryOp, Loc, Loc, Loc),

    JUMP(String),
    DJUMP(Loc),
    BRANCHON(Value, String, Loc),

    PRINT(Loc),
    READ(Type, Loc),

    EXIT,
}

// impl From<&str> for Instruction

// tests ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[cfg(test)]
mod test {
    use super::*;
    use super::UnaryOp::*;
    use super::BinaryOp::*;
    const DEFAULT_ERROR: OpApplicationError = OpApplicationError::BadBinaryOp(BinaryOp::ADD, Value::I32(0), Value::I32(0));

    // #[test]
    // fn apply_unary_test_1() {
    //     let val = Value::I32(1);
    //     assert_eq!(apply_unary!(I32, val, I32, -)(DEFAULT_ERROR).unwrap(), Value::I32(-1));
    // }

    // #[test]
    // fn apply_unary_test_2() {
    //     let val = Value::F32(3.14159);
    //     assert_eq!(apply_unary!(F32, val, F32, -)(DEFAULT_ERROR).unwrap(), Value::F32(-3.14159));
    // }

    // #[test]
    // fn apply_unary_test_3() {
    //     let val = Value::Bool(false);
    //     assert_eq!(apply_unary!(Bool, val, Bool, !)(DEFAULT_ERROR).unwrap(), Value::Bool(true));
    // }

    // #[test]
    // fn apply_unary_test_5() {
    //     let val = Value::Char('c');
    //     assert!(apply_unary!(I32, val, I32, -)(DEFAULT_ERROR).is_err());
    // }

    // #[test]
    // fn apply_unary_test_6() {
    //     let val = Value::I32(1);
    //     assert!(apply_unary!(Bool, val, Bool, !)(DEFAULT_ERROR).is_err());
    // }

    // #[test]
    // fn apply_unary_test_7() {
    //     let val = Value::I32(3);
    //     assert!(apply_unary!(F32, val, F32, -)(DEFAULT_ERROR).is_err());
    // }

    #[test]
    fn apply_binary_test_1() {
        let lhs = Value::I32(1);
        let rhs = Value::I32(2);
        assert_eq!(apply_binary!(I32, lhs, I32, rhs, I32, +)(DEFAULT_ERROR).unwrap(), Value::I32(3));
    }

    #[test]
    fn apply_binary_test_2() {
        let lhs_val = 3.14159;
        let rhs_val = 2.71828;
        let lhs = Value::F32(lhs_val);
        let rhs = Value::F32(rhs_val);
        assert_eq!(apply_binary!(F32, lhs, F32, rhs, F32, -)(DEFAULT_ERROR).unwrap(), Value::F32(lhs_val - rhs_val));
    }

    #[test]
    fn apply_binary_test_3() {
        let lhs = Value::Char('a');
        let rhs = Value::Char('b');
        assert_eq!(apply_binary!(Char, lhs, Char, rhs, Bool, <)(DEFAULT_ERROR).unwrap(), Value::Bool(true));
    }

    #[test]
    fn apply_binary_test_4() {
        let lhs = Value::I32(2);
        let rhs = Value::I32(4);
        assert_eq!(apply_binary!(I32, lhs, I32, rhs, I32, |)(DEFAULT_ERROR).unwrap(), Value::I32(6));
    }

    #[test]
    fn apply_binary_test_5() {
        let lhs = Value::F32(3.14);
        let rhs = Value::F32(3.14);
        assert_eq!(apply_binary!(F32, lhs, F32, rhs, Bool, ==)(DEFAULT_ERROR).unwrap(), Value::Bool(true));
    }

    #[test]
    fn apply_binary_test_6() {
        let lhs = Value::I32(3);
        let rhs = Value::I32(4);
        assert!(apply_binary!(F32, lhs, F32, rhs, F32, +)(DEFAULT_ERROR).is_err());
    }

    #[test]
    fn apply_binary_test_7() {
        let lhs = Value::Bool(true);
        let rhs = Value::Bool(false);
        assert!(apply_binary!(I32, lhs, I32, rhs, I32, &)(DEFAULT_ERROR).is_err());
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
        let val = Value::I32(0x0f0f0f0f << 4);
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
    fn cvt_i32_test_1() {
        let val = Value::I32(3);
        assert_eq!(CVT(Type::I32).apply_to(val).unwrap(), val);
    }

    #[test]
    fn cvt_i32_test_2() {
        let val = Value::F32(3.14);
        assert_eq!(CVT(Type::I32).apply_to(val).unwrap(), Value::I32(3));
    }

    #[test]
    fn cvt_i32_test_3() {
        let val = Value::Char('a');
        assert_eq!(CVT(Type::I32).apply_to(val).unwrap(), Value::I32(97));
    }

    #[test]
    fn cvt_i32_test_4() {
        let val = Value::Bool(true);
        assert_eq!(CVT(Type::I32).apply_to(val).unwrap(), Value::I32(1));
    }

    #[test]
    fn cvt_i32_test_5() {
        let val = Value::Bool(false);
        assert_eq!(CVT(Type::I32).apply_to(val).unwrap(), Value::I32(0));
    }

    #[test]
    fn cvt_i32_test_6() {
        let val = Value::IPtr(1234);
        assert_eq!(CVT(Type::I32).apply_to(val).unwrap(), Value::I32(1234));
    }

    #[test]
    fn cvt_i32_test_7() {
        let val = Value::SPtr(1234);
        assert_eq!(CVT(Type::I32).apply_to(val).unwrap(), Value::I32(1234));
    }

    #[test]
    fn cvt_i32_test_8() {
        let val = Value::Void;
        assert!(CVT(Type::I32).apply_to(val).is_err());
    }

    #[test]
    fn cvt_f32_test_1() {
        let val = Value::I32(4);
        assert_eq!(CVT(Type::F32).apply_to(val).unwrap(), Value::F32(4.0));
    }

    #[test]
    fn cvt_f32_test_2() {
        let val = Value::F32(2.71828);
        assert_eq!(CVT(Type::F32).apply_to(val).unwrap(), Value::F32(2.71828));
    }

    #[test]
    fn cvt_f32_test_3() {
        let val = Value::Char('c');
        assert!(CVT(Type::F32).apply_to(val).is_err());
    }

    #[test]
    fn cvt_f32_test_4() {
        let val = Value::Bool(true);
        assert!(CVT(Type::F32).apply_to(val).is_err());
    }

    #[test]
    fn cvt_f32_test_5() {
        let val = Value::IPtr(0x1);
        assert!(CVT(Type::F32).apply_to(val).is_err());
    }

    #[test]
    fn cvt_f32_test_6() {
        let val = Value::SPtr(0x1);
        assert!(CVT(Type::F32).apply_to(val).is_err());
    }

    #[test]
    fn cvt_f32_test_7() {
        let val = Value::Void;
        assert!(CVT(Type::F32).apply_to(val).is_err());
    }

    #[test]
    fn cvt_char_test_1() {
        let val = Value::I32(65);
        assert!(CVT(Type::Char).apply_to(val).is_err());
    }

    #[test]
    fn cvt_char_test_2() {
        let val = Value::F32(3.14159);
        assert!(CVT(Type::Char).apply_to(val).is_err());
    }

    #[test]
    fn cvt_char_test_3() {
        let val = Value::Char('x');
        assert_eq!(CVT(Type::Char).apply_to(val).unwrap(), Value::Char('x'));
    }

    #[test]
    fn cvt_char_test_4() {
        let val = Value::Bool(true);
        assert!(CVT(Type::Char).apply_to(val).is_err());
    }

    #[test]
    fn cvt_char_test_5() {
        let val = Value::IPtr(0x3);
        assert!(CVT(Type::Char).apply_to(val).is_err());
    }

    #[test]
    fn cvt_char_test_6() {
        let val = Value::SPtr(0x3);
        assert!(CVT(Type::Char).apply_to(val).is_err());
    }

    #[test]
    fn cvt_char_test_7() {
        let val = Value::Void;
        assert!(CVT(Type::Char).apply_to(val).is_err());
    }

    #[test]
    fn cvt_bool_test_1() {
        let val = Value::I32(0);
        assert_eq!(CVT(Type::Bool).apply_to(val).unwrap(), Value::Bool(false));
    }

    #[test]
    fn cvt_bool_test_2() {
        let val = Value::I32(4);
        assert_eq!(CVT(Type::Bool).apply_to(val).unwrap(), Value::Bool(true));
    }

    #[test]
    fn cvt_bool_test_3() {
        let val = Value::F32(0.0);
        assert_eq!(CVT(Type::Bool).apply_to(val).unwrap(), Value::Bool(false));
    }

    #[test]
    fn cvt_bool_test_4() {
        let val = Value::F32(1.0);
        assert_eq!(CVT(Type::Bool).apply_to(val).unwrap(), Value::Bool(true));
    }

    #[test]
    fn cvt_bool_test_5() {
        let val = Value::Char('\0');
        assert_eq!(CVT(Type::Bool).apply_to(val).unwrap(), Value::Bool(false));
    }

    #[test]
    fn cvt_bool_test_6() {
        let val = Value::Char('\n');
        assert_eq!(CVT(Type::Bool).apply_to(val).unwrap(), Value::Bool(true));
    }

    #[test]
    fn cvt_bool_test_7() {
        let val = Value::Bool(false);
        assert_eq!(CVT(Type::Bool).apply_to(val).unwrap(), Value::Bool(false));
    }

    #[test]
    fn cvt_bool_test_8() {
        let val = Value::Bool(true);
        assert_eq!(CVT(Type::Bool).apply_to(val).unwrap(), Value::Bool(true));
    }

    #[test]
    fn cvt_bool_test_9() {
        let val = Value::IPtr(0x0);
        assert_eq!(CVT(Type::Bool).apply_to(val).unwrap(), Value::Bool(false));
    }

    #[test]
    fn cvt_bool_test_10() {
        let val = Value::IPtr(0x8);
        assert_eq!(CVT(Type::Bool).apply_to(val).unwrap(), Value::Bool(true));
    }

    #[test]
    fn cvt_bool_test_11() {
        let val = Value::SPtr(0x0);
        assert_eq!(CVT(Type::Bool).apply_to(val).unwrap(), Value::Bool(false));
    }

    #[test]
    fn cvt_bool_test_12() {
        let val = Value::SPtr(0x8);
        assert_eq!(CVT(Type::Bool).apply_to(val).unwrap(), Value::Bool(true));
    }

    #[test]
    fn cvt_bool_test_13() {
        let val = Value::Void;
        assert!(CVT(Type::Bool).apply_to(val).is_err());
    }

    #[test]
    fn cvt_iptr_test_1() {
        let val = Value::I32(254);
        assert_eq!(CVT(Type::IPtr).apply_to(val).unwrap(), Value::IPtr(254));
    }

    #[test]
    fn cvt_iptr_test_2() {
        let val = Value::F32(2.54);
        assert!(CVT(Type::IPtr).apply_to(val).is_err());
    }

    #[test]
    fn cvt_iptr_test_3() {
        let val = Value::Char('b');
        assert!(CVT(Type::IPtr).apply_to(val).is_err());
    }

    #[test]
    fn cvt_iptr_test_4() {
        let val = Value::Bool(false);
        assert!(CVT(Type::IPtr).apply_to(val).is_err());
    }

    #[test]
    fn cvt_iptr_test_5() {
        let val = Value::IPtr(0x754);
        assert_eq!(CVT(Type::IPtr).apply_to(val).unwrap(), Value::IPtr(0x754));
    }

    #[test]
    fn cvt_iptr_test_6() {
        let val = Value::SPtr(0x754);
        assert!(CVT(Type::IPtr).apply_to(val).is_err());
    }

    #[test]
    fn cvt_iptr_test_7() {
        let val = Value::Void;
        assert!(CVT(Type::IPtr).apply_to(val).is_err());
    }

    #[test]
    fn cvt_sptr_test_1() {
        let val = Value::I32(254);
        assert_eq!(CVT(Type::SPtr).apply_to(val).unwrap(), Value::SPtr(254));
    }

    #[test]
    fn cvt_sptr_test_2() {
        let val = Value::F32(2.54);
        assert!(CVT(Type::SPtr).apply_to(val).is_err());
    }

    #[test]
    fn cvt_sptr_test_3() {
        let val = Value::Char('b');
        assert!(CVT(Type::SPtr).apply_to(val).is_err());
    }

    #[test]
    fn cvt_sptr_test_4() {
        let val = Value::Bool(false);
        assert!(CVT(Type::SPtr).apply_to(val).is_err());
    }

    #[test]
    fn cvt_sptr_test_5() {
        let val = Value::IPtr(0x754);
        assert!(CVT(Type::SPtr).apply_to(val).is_err());
    }

    #[test]
    fn cvt_sptr_test_6() {
        let val = Value::SPtr(0x754);
        assert_eq!(CVT(Type::SPtr).apply_to(val).unwrap(), Value::SPtr(0x754));
    }

    #[test]
    fn cvt_sptr_test_7() {
        let val = Value::Void;
        assert!(CVT(Type::SPtr).apply_to(val).is_err());
    }

    #[test]
    fn cvt_void_test_1() {
        let val = Value::I32(3);
        assert!(CVT(Type::Void).apply_to(val).is_err());
    }

    #[test]
    fn cvt_void_test_2() {
        let val = Value::F32(4.32);
        assert!(CVT(Type::Void).apply_to(val).is_err());
    }

    #[test]
    fn cvt_void_test_3() {
        let val = Value::Char('c');
        assert!(CVT(Type::Void).apply_to(val).is_err());
    }

    #[test]
    fn cvt_void_test_4() {
        let val = Value::Bool(false);
        assert!(CVT(Type::Void).apply_to(val).is_err());
    }

    #[test]
    fn cvt_void_test_5() {
        let val = Value::IPtr(0x385);
        assert!(CVT(Type::Void).apply_to(val).is_err());
    }

    #[test]
    fn cvt_void_test_6() {
        let val = Value::SPtr(0x385);
        assert!(CVT(Type::Void).apply_to(val).is_err());
    }

    #[test]
    fn cvt_void_test_7() {
        let val = Value::Void;
        assert_eq!(CVT(Type::Void).apply_to(val).unwrap(), Value::Void);
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
