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

// cookie data types and value ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

macro_rules! define_types {
    [$( ($n:ident,$t:ty) ),+] => {
        #[derive(Debug,Clone,Copy,PartialEq)]
        pub enum Type { $($n),+ , Void }

        #[allow(non_snake_case)]
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

impl UnaryOp {
    pub fn apply_to(&self, val: Value) -> result::Result<Value,OpApplicationError> {
        let apply_err = OpApplicationError::BadUnaryOp(self.clone(),val);

        let v = match self {
            UnaryOp::NEG => match val {
                Value::I32(v) => Value::I32(-v),
                Value::F32(v) => Value::F32(-v),
                _ => return Err(apply_err),
            }
            UnaryOp::NOT => match val {
                Value::Bool(v) => Value::Bool(!v),
                Value::I32(v) => Value::I32(!v),
                _ => return Err(apply_err),
            }
            UnaryOp::CVT(t) => val.convert_to(*t)?
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

        macro_rules! implement_for {
            [ $( ($l:ident, $r:ident, $res:ident, $op:tt) ),+ ] => {
                match (lhs, rhs) {
                    $( (Value::$l(l), Value::$r(r)) => Ok(Value::$res($op(l,r))) ),+ ,
                    _ => apply_err
                }
            };
        }

        match self {
            BinaryOp::ADD => implement_for![
                (I32, I32, I32, (|l,r| l + r)),
                (F32, F32, F32, (|l,r| l + r)),
                (IPtr, I32, IPtr, ptr_add),
                (SPtr, I32, SPtr, ptr_add)
            ],
            BinaryOp::SUB => implement_for![
                (I32, I32, I32, (|l,r| l - r)),
                (F32, F32, F32, (|l,r| l - r)),
                (IPtr, I32, IPtr, ptr_sub),
                (SPtr, I32, SPtr, ptr_sub)
            ],
            BinaryOp::MUL => implement_for![
                (I32, I32, I32, (|l,r| l * r)),
                (F32, F32, F32, (|l,r| l * r))
            ],
            BinaryOp::DIV =>implement_for![
                (I32, I32, I32, (|l,r| l / r)),
                (F32, F32, F32, (|l,r| l / r))
            ],
            BinaryOp::MOD => implement_for![
                (I32, I32, I32, (|l,r| l % r)),
                (F32, F32, F32, (|l,r| l % r))
            ],
            BinaryOp::EQ => match (lhs, rhs) {
                (Value::Void, Value::Void) => Ok(Value::Bool(true)),
                _ => implement_for![
                    (I32, I32, Bool, (|l,r| l == r)),
                    (F32, F32, Bool, (|l,r| l == r)),
                    (Char, Char, Bool, (|l,r| l == r)),
                    (Bool, Bool, Bool, (|l,r| l == r)),
                    (IPtr, IPtr, Bool, (|l,r| l == r)),
                    (SPtr, SPtr, Bool, (|l,r| l == r))
                ]
            },
            BinaryOp::LT => implement_for![
                (I32, I32, Bool, (|l,r| l < r)),
                (F32, F32, Bool, (|l,r| l < r)),
                (Char, Char, Bool, (|l,r| l < r))
            ],
            BinaryOp::LE => implement_for![
                (I32, I32, Bool, (|l,r| l <= r)),
                (F32, F32, Bool, (|l,r| l <= r)),
                (Char, Char, Bool, (|l,r| l <= r))
            ],
            BinaryOp::GT => implement_for![
                (I32, I32, Bool, (|l,r| l > r)),
                (F32, F32, Bool, (|l,r| l > r)),
                (Char, Char, Bool, (|l,r| l > r))
            ],
            BinaryOp::GE => implement_for![
                (I32, I32, Bool, (|l,r| l >= r)),
                (F32, F32, Bool, (|l,r| l >= r)),
                (Char, Char, Bool, (|l,r| l >= r))
            ],
            BinaryOp::AND => implement_for![
                (Bool, Bool, Bool, (|l,r| l && r)),
                (I32, I32, I32, (|l,r| l & r))
            ],
            BinaryOp::OR => implement_for![
                (Bool, Bool, Bool, (|l,r| l || r)),
                (I32, I32, I32, (|l,r| l | r))
            ],
            BinaryOp::XOR => implement_for![
                (Bool, Bool, Bool, (|l,r| l != r)),
                (I32, I32, I32, (|l,r| l ^ r))
            ],
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
pub enum Target {
    UnresolvedLabel(String),
    InternalLabel(usize, String),
    ExternalLabel(usize, String)
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

    JUMP(Target),
    DJUMP(Loc),
    BRANCHON(Value, Target, Loc),

    PRINT(Loc),
    READ(Type, Loc),

    EXIT,
}

// tests ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#[cfg(test)]
mod test {
    use super::*;
    use super::UnaryOp::*;
    use super::BinaryOp::*;

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
