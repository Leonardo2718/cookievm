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

use cookie_base::*;
use interpreter::*;
use std::fmt;
use std::str::Chars;
use std::iter::Iterator;
use std::collections::HashMap;

// impl FromStr for Value {
//     type Err = String;
//     fn from_str(s: &str) -> result::Result<Self,Self::Err> {
//         use self::Value::*;
//         let is_identifier =  |c: &char| c.is_alphanumeric() || c == &'_';
//         let s_iter = s.trim().chars();
//         match s_iter.clone().take_while(is_identifier).collect::<String>().as_ref() {
//             "I32" => {
//                 let mut s_iter = s_iter.skip(3).skip_while(|c| c.is_whitespace());
//                 assert_next_char_is(&s_iter, '(');
//                 // let c = s_iter.next().ok_or("Expecting more characters")?;
//                 // if c != '(' { return Err(format!("Unexpected character {}", c)); }
//                 let s_iter = s_iter.skip_while(|c| c.is_whitespace());
//                 let ss = s_iter.clone().take_while(|c| c.is_numeric()).collect::<String>();
//                 let c = s_iter.skip(ss.len()).skip_while(|c| c.is_whitespace()).next().ok_or("Expected more characters")?;
//                 if c != ')' { return Err(format!("Unexpected character {}", c)); }
//                 let v = ss.parse::<i32>().or(Err(format!("Failed to parse {}", ss)))?;
//                 Ok(I32(v))
//             },
//             n =>  Err(format!("Could not match {}", n))
//         }
//     }
// }

#[derive(Debug,Clone,PartialEq)]
pub enum OpToken {

}

#[derive(Debug,Clone,PartialEq)]
pub enum Token {
    Ident(String),
    Label(String),
    Integer(i32),
    Float(f32),
    Address(usize),
    Char(char),
    Bool(bool),
    Void,
    SP,
    FP,
    PC,
    R(u8),
    LParen,
    RParen,
    Dot,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

pub type TokenList = Vec<Token>;

macro_rules! eat_while {
    ($iter:expr, $pred:expr, $eater:expr) => (
        loop {
            match $iter.clone().peekable().peek() {
                Some(c) if $pred(c) => {$iter.next(); $eater(c)},
                _ => break,
            }
        }
    )
}

macro_rules! skip_n {
    ($iter:expr, $count:expr) => (
        for i in 0..$count { $iter.next(); }
    )
}

macro_rules! peek {
    ($iter:expr) => (
        $iter.clone().peekable().peek()
    )
}

pub struct Lexer<'a> {
    iter: Chars<'a>,
}

impl<'a> Lexer<'a> {
    pub fn new<'b>(iter: Chars<'b>) -> Lexer<'b> {
        Lexer{iter: iter}
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        loop {
            match peek!(self.iter) {
                Some(&'(') => { skip_n!(self.iter,1); return Some(Token::LParen); }
                Some(&')') => { skip_n!(self.iter,1); return Some(Token::RParen); }
                Some(&'.') => { skip_n!(self.iter,1); return Some(Token::Dot); }
                Some(&';') => { eat_while!(self.iter.by_ref(), |c| c != &'\n', |_| ()); skip_n!(self.iter,1); continue; }
                Some(c) if c.is_whitespace() => { skip_n!(self.iter,1); continue; }
                Some(&'\'') => {
                    skip_n!(self.iter,1);
                    let c = match self.iter.next() {
                        Some('\\') => {
                            match self.iter.next() {
                                Some('\'') => '\'',
                                Some('\\') => '\\',
                                Some('t') => '\t',
                                Some('n') => '\n',
                                Some('r') => '\r',
                                Some(c) => c,
                                None => return None
                            }
                        },
                        Some(c) => c,
                        _ => return None
                    };
                    return match self.iter.next() {
                        Some('\'') => Some(Token::Char(c)),
                        _ => None
                    };
                }
                Some(&'$') => {
                    skip_n!(self.iter, 1);
                    let mut s = String::new();
                    match self.iter.clone().peekable().peek() {
                        Some(c) if c.is_numeric() => {
                            let is_gpr = |c:&char| c.is_numeric();
                            eat_while!(self.iter, is_gpr, |c:&char| s.push(*c));
                            return u8::from_str_radix(s.as_ref(), 10).ok().map(|i:u8| Token::R(i));
                        },
                        Some(c) if c.is_alphabetic() => {
                            let is_reg = |c:&char| c.is_alphabetic();
                            eat_while!(self.iter, is_reg, |c:&char| s.push(*c));
                            return match s.as_ref() {
                                 "sp" => Some(Token::SP),
                                 "fp" => Some(Token::FP),
                                 "pc" => Some(Token::PC),
                                 _ => None
                            }
                        }
                        _ => return None
                    }
                }
                Some(c) if c.is_alphabetic() || c == &'_' => {
                    let mut s = String::new();
                    let is_ident = |c:&char| c.is_alphanumeric() || c == &'_';
                    eat_while!(self.iter.by_ref(), is_ident, |c:&char| s.push(*c));
                    return match s.to_lowercase().as_ref() {
                        "true" => Some(Token::Bool(true)),
                        "false" => Some(Token::Bool(false)),
                        "void" => Some(Token::Void),
                        _ => match peek!(self.iter) {
                            Some(&':') => { skip_n!(self.iter, 1); Some(Token::Label(s)) },
                            _ => Some(Token::Ident(s))
                        }
                    }
                }
                Some(c) if c.is_digit(10) => {
                    let mut s = String::new();
                    let mut iter_clone = self.iter.clone();
                    match (iter_clone.next(), iter_clone.next()) {
                        (Some('0'), Some('x')) => {
                            skip_n!(self.iter,2);
                            let is_hex = |c:&char| c.is_digit(16);
                            eat_while!(self.iter.by_ref(), is_hex, |c:&char| s.push(*c));
                            return usize::from_str_radix(s.as_ref(), 16).ok().map(|a:usize| Token::Address(a));
                        }
                        _ => {
                            let is_num = |c:&char| c.is_digit(10);
                            eat_while!(self.iter.by_ref(), is_num, |c:&char| s.push(*c));
                            match self.iter.clone().peekable().peek() {
                                Some('.') => {
                                    skip_n!(self.iter,1);
                                    s.push('.');
                                    eat_while!(self.iter.by_ref(), is_num, |c:&char| s.push(*c));
                                    return s.clone().parse::<f32>().ok().map(|f:f32| Token::Float(f));
                                },
                                _ => {
                                    return s.clone().parse::<i32>().ok().map(|i:i32| Token::Integer(i));
                                }
                            }
                        }
                    }
                }
                _ => { return None; }
            }
        }
    }
}

macro_rules! eat_token_ {
    ($iter:expr, $expect:tt) => ({
        let t = $iter.next();
        match t {
            Some(Token::$expect) => Ok(t.unwrap()),
            Some(t) => Err(format!("Unexpected token: {}", t)),
            None => Err(format!("Unexpected end of token stream"))
        }
    })
}

macro_rules! unexpected_token ( ($t:expr)  => (Err(format!("Unexpected token: {}", $t))) );
macro_rules! unexpected_id    ( ($id:expr) => (Err(format!("Unexpected identifier: {}", $id))) );
macro_rules! unexpected_end   ( ()         => {Err(format!("Unexpected end of token stream"))} );

macro_rules! eat_token {
    ($iter:expr, $expect:tt) => ({
        let t = $iter.next();
        match t {
            Some(Token::$expect(v)) => Ok(v),
            Some(t) => unexpected_token!(t),
            None => unexpected_end!(),
        }
    })
}

fn parse_stack_op<'a>(lexer: &mut Lexer<'a>) -> Result<Instruction> {
    use cookie_base::Instruction::*;
    use cookie_base::UnaryOp::*;
    use cookie_base::BinaryOp::*;
    let id = eat_token!(lexer, Ident)?;
    let inst = match id.to_lowercase().as_ref() {
        "neg" => UOp(NEG, Loc::Stack, Loc::Stack),
        "not" => UOp(NOT, Loc::Stack, Loc::Stack),
        "add" => BOp(ADD, Loc::Stack, Loc::Stack, Loc::Stack),
        "sub" => BOp(SUB, Loc::Stack, Loc::Stack, Loc::Stack),
        "mul" => BOp(MUL, Loc::Stack, Loc::Stack, Loc::Stack),
        "div" => BOp(DIV, Loc::Stack, Loc::Stack, Loc::Stack),
        "mod" => BOp(MOD, Loc::Stack, Loc::Stack, Loc::Stack),
        "eq" => BOp(EQ, Loc::Stack, Loc::Stack, Loc::Stack),
        "lt" => BOp(LT, Loc::Stack, Loc::Stack, Loc::Stack),
        "le" => BOp(LE, Loc::Stack, Loc::Stack, Loc::Stack),
        "gt" => BOp(GT, Loc::Stack, Loc::Stack, Loc::Stack),
        "ge" => BOp(GE, Loc::Stack, Loc::Stack, Loc::Stack),
        "and" => BOp(AND, Loc::Stack, Loc::Stack, Loc::Stack),
        "or" => BOp(OR, Loc::Stack, Loc::Stack, Loc::Stack),
        "xor" => BOp(XOR, Loc::Stack, Loc::Stack, Loc::Stack),
        id => return unexpected_id!(id)
    };
    Ok(inst)
}

fn parse_value<'a>(lexer: &mut Lexer<'a>) -> Result<Value> {
    macro_rules! parse_as (
        ($id:tt, $val:tt) => ({
            eat_token_!(lexer, LParen)?;
            let v = eat_token!(lexer, $id)?;
            eat_token_!(lexer, RParen)?;
            Ok(Value::$val(v))
        })
    );

    match lexer.next().clone() {
        Some(Token::Void) => Ok(Value::Void),
        Some(Token::Ident(id)) => match id.to_lowercase().as_ref() {
            "i32" => parse_as!(Integer, I32),
            "f32" => parse_as!(Float, F32),
            "char" => parse_as!(Char, Char),
            "bool" => parse_as!(Bool, Bool),
            "iptr" => parse_as!(Address, IPtr),
            "sptr" => parse_as!(Address, SPtr),
            id => return unexpected_id!(id)
        },
        Some(t) => return unexpected_token!(t),
        None => return unexpected_end!()
    }
}

fn parse_register<'a>(lexer: &mut Lexer<'a>) -> Result<RegisterName> {
    match lexer.next().clone() {
        Some(Token::SP) => Ok(RegisterName::StackPointer),
        Some(Token::FP) => Ok(RegisterName::FramePointer),
        Some(Token::PC) => Ok(RegisterName::ProgramCounter),
        Some(Token::R(i)) => Ok(RegisterName::R(i)),
        Some(t) => unexpected_token!(t),
        None => unexpected_end!()
    }
}

fn parse_type<'a>(lexer: &mut Lexer<'a>) -> Result<Type> {
    match lexer.next().clone() {
        Some(Token::Void) => Ok(Type::Void),
        Some(Token::Ident(id)) => match id.to_lowercase().as_ref() {
            "i32" => Ok(Type::I32),
            "f32" => Ok(Type::F32),
            "char" => Ok(Type::Char),
            "bool" => Ok(Type::Bool),
            "iptr" => Ok(Type::IPtr),
            "sptr" => Ok(Type::SPtr),
            id => return unexpected_id!(id),
        }
        Some(t) => return unexpected_token!(t),
        None => return unexpected_end!(),
    }
}

pub fn parse<'a>(mut lexer: Lexer<'a>) -> Result<(InstructionList, LabelTable)> {
    use cookie_base::Instruction::*;

    let mut insts: InstructionList = Vec::new();
    let mut labels: LabelTable = HashMap::new();

    loop {
        match lexer.next().clone() {
            Some(Token::Ident(id)) => match id.to_lowercase().as_ref() {
                "s" => {
                    eat_token_!(lexer, Dot)?;
                    let inst = parse_stack_op(&mut lexer)?;
                    insts.push(inst);
                },
                "pushc" => {
                    let val = parse_value(&mut lexer)?;
                    insts.push(PUSHC(val));
                },
                "pushr" => {
                    let reg = parse_register(&mut lexer)?;
                    insts.push(PUSHR(reg));
                },
                "popr" => {
                    let reg = parse_register(&mut lexer)?;
                    insts.push(POPR(reg));
                },
                "pop" => { insts.push(POP); },
                "loadfrom" => { insts.push(LOADFROM(Loc::Stack, Loc::Stack)); },
                "storeto" => { insts.push(STORETO(Loc::Stack, Loc::Stack)); },
                "jump" => { let l = eat_token!(lexer, Ident)?; insts.push(JUMP(l)); },
                "djump" => { insts.push(DJUMP(Loc::Stack)); },
                "branchon" => {
                    let v = parse_value(&mut lexer)?;
                    let l = eat_token!(lexer, Ident)?;
                    insts.push(BRANCHON(v, l, Loc::Stack));
                },
                "print" => { insts.push(PRINT(Loc::Stack)); }
                "read" => { let t = parse_type(&mut lexer)?; insts.push(READ(t, Loc::Stack)); }
                "exit" => { insts.push(EXIT); }
                id => return unexpected_id!(id)
            },
            Some(Token::Label(l)) => { labels.insert(l.to_string(), insts.len()); },
            Some(t) => return unexpected_token!(t),
            None => break,
        };
    }

    return Ok((insts, labels));
}

#[cfg(test)]
mod test {
    use super::*;
    use cookie_base::Instruction::*;

    #[test]
    fn lexer_test_1() {
        let mut lexer = Lexer::new("1234".chars());
        assert_eq!(lexer.next().unwrap(), Token::Integer(1234));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_2() {
        let mut lexer = Lexer::new("I32".chars());
        assert_eq!(lexer.next().unwrap(), Token::Ident("I32".to_string()));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_3() {
        let mut lexer = Lexer::new("2.71828".chars());
        assert_eq!(lexer.next().unwrap(), Token::Float(2.71828));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_4() {
        let mut lexer = Lexer::new("0xabcd1234".chars());
        assert_eq!(lexer.next().unwrap(), Token::Address(0xabcd1234));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_5() {
        let mut lexer = Lexer::new("(".chars());
        assert_eq!(lexer.next().unwrap(), Token::LParen);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_6() {
        let mut lexer = Lexer::new(")".chars());
        assert_eq!(lexer.next().unwrap(), Token::RParen);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_7() {
        let mut lexer = Lexer::new(".".chars());
        assert_eq!(lexer.next().unwrap(), Token::Dot);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_8() {
        let mut lexer = Lexer::new("'e'".chars());
        assert_eq!(lexer.next().unwrap(), Token::Char('e'));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_9() {
        let mut lexer = Lexer::new(r"'\n'".chars());
        assert_eq!(lexer.next().unwrap(), Token::Char('\n'));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_10() {
        let mut lexer = Lexer::new(r"'\f'".chars());
        assert_eq!(lexer.next().unwrap(), Token::Char('f'));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_11() {
        let mut lexer = Lexer::new(r"'\\'".chars());
        assert_eq!(lexer.next().unwrap(), Token::Char('\\'));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_12() {
        let mut lexer = Lexer::new("foo:".chars());
        assert_eq!(lexer.next().unwrap(), Token::Label("foo".to_string()));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_13() {
        let mut lexer = Lexer::new("true".chars());
        assert_eq!(lexer.next().unwrap(), Token::Bool(true));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_14() {
        let mut lexer = Lexer::new("false".chars());
        assert_eq!(lexer.next().unwrap(), Token::Bool(false));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_15() {
        let mut lexer = Lexer::new(" F32 ( 3.14159 ) ".chars());
        assert_eq!(lexer.next().unwrap(), Token::Ident("F32".to_string()));
        assert_eq!(lexer.next().unwrap(), Token::LParen);
        assert_eq!(lexer.next().unwrap(), Token::Float(3.14159));
        assert_eq!(lexer.next().unwrap(), Token::RParen);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_16() {
        let mut lexer = Lexer::new("0xabcdefg".chars());
        assert_eq!(lexer.next().unwrap(), Token::Address(0xabcdef));
        assert_eq!(lexer.next().unwrap(), Token::Ident("g".to_string()));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_17() {
        let mut lexer = Lexer::new("true:".chars());
        assert_eq!(lexer.next().unwrap(), Token::Bool(true));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_18() {
        let mut lexer = Lexer::new("foo0x123".chars());
        assert_eq!(lexer.next().unwrap(), Token::Ident("foo0x123".to_string()));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_19() {
        let mut lexer = Lexer::new("; some text".chars());
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_20() {
        let mut lexer = Lexer::new(r"'\n' ; 0x123".chars());
        assert_eq!(lexer.next().unwrap(), Token::Char('\n'));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_21() {
        let mut lexer = Lexer::new("Void".chars());
        assert_eq!(lexer.next().unwrap(), Token::Void);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_22() {
        let mut lexer = Lexer::new("I32(3)".chars());
        assert_eq!(lexer.next().unwrap(), Token::Ident("I32".to_string()));
        assert_eq!(lexer.next().unwrap(), Token::LParen);
        assert_eq!(lexer.next().unwrap(), Token::Integer(3));
        assert_eq!(lexer.next().unwrap(), Token::RParen);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_23() {
        let mut lexer = Lexer::new("$sp".chars());
        assert_eq!(lexer.next().unwrap(), Token::SP);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_24() {
        let mut lexer = Lexer::new("$fp".chars());
        assert_eq!(lexer.next().unwrap(), Token::FP);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_25() {
        let mut lexer = Lexer::new("$pc".chars());
        assert_eq!(lexer.next().unwrap(), Token::PC);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_26() {
        let mut lexer = Lexer::new("$0".chars());
        assert_eq!(lexer.next().unwrap(), Token::R(0));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_27() {
        let mut lexer = Lexer::new(" foo L1: bar".chars());
        assert_eq!(lexer.next().unwrap(), Token::Ident("foo".to_string()));
        assert_eq!(lexer.next().unwrap(), Token::Label("L1".to_string()));
        assert_eq!(lexer.next().unwrap(), Token::Ident("bar".to_string()));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_28() {
        let mut lexer = Lexer::new("L1:L2:".chars());
        assert_eq!(lexer.next().unwrap(), Token::Label("L1".to_string()));
        assert_eq!(lexer.next().unwrap(), Token::Label("L2".to_string()));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn parse_stack_op_test_1() {
        let inst = parse_stack_op(&mut Lexer::new("Add".chars())).unwrap();
        assert_eq!(inst, Instruction::BOp(BinaryOp::ADD, Loc::Stack, Loc::Stack, Loc::Stack));
    }

    #[test]
    fn parse_stack_op_test_2() {
        let inst = parse_stack_op(&mut Lexer::new("EQ".chars())).unwrap();
        assert_eq!(inst, Instruction::BOp(BinaryOp::EQ, Loc::Stack, Loc::Stack, Loc::Stack));
    }

    #[test]
    fn parse_stack_op_test_3() {
        let inst = parse_stack_op(&mut Lexer::new("NOT".chars())).unwrap();
        assert_eq!(inst, Instruction::UOp(UnaryOp::NOT, Loc::Stack, Loc::Stack));
    }

    #[test]
    fn parse_stack_op_test_4() {
        assert!(parse_stack_op(&mut Lexer::new("foo".chars())).is_err());
    }

    #[test]
    fn parse_value_test_1() {
        let val = parse_value(&mut Lexer::new("I32(3)".chars())).unwrap();
        assert_eq!(val, Value::I32(3));
    }

    #[test]
    fn parse_value_test_2() {
        let val = parse_value(&mut Lexer::new("F32(2.71828)".chars())).unwrap();
        assert_eq!(val, Value::F32(2.71828));
    }

    #[test]
    fn parse_value_test_3() {
        let val = parse_value(&mut Lexer::new(r"Char('\\')".chars())).unwrap();
        assert_eq!(val, Value::Char('\\'));
    }

    #[test]
    fn parse_value_test_4() {
        let val = parse_value(&mut Lexer::new("Bool(False)".chars())).unwrap();
        assert_eq!(val, Value::Bool(false));
    }

    #[test]
    fn parse_value_test_5() {
        let val = parse_value(&mut Lexer::new("IPtr(0xabc)".chars())).unwrap();
        assert_eq!(val, Value::IPtr(0xabc));
    }

    #[test]
    fn parse_value_test_6() {
        let val = parse_value(&mut Lexer::new("SPtr(0x123)".chars())).unwrap();
        assert_eq!(val, Value::SPtr(0x123));
    }

    #[test]
    fn parse_value_test_7() {
        let val = parse_value(&mut Lexer::new("Void".chars())).unwrap();
        assert_eq!(val, Value::Void);
    }

    #[test]
    fn parse_value_test_8() {
        assert!(parse_value(&mut Lexer::new("foo".chars())).is_err());
    }

    #[test]
    fn parse_value_test_9() {
        assert!(parse_value(&mut Lexer::new("I32(2.0)".chars())).is_err());
    }

    #[test]
    fn parse_value_test_10() {
        assert!(parse_value(&mut Lexer::new("F32(4)".chars())).is_err());
    }

    #[test]
    fn parse_value_test_11() {
        assert!(parse_value(&mut Lexer::new("Char(c)".chars())).is_err());
    }

    #[test]
    fn parse_value_test_12() {
        assert!(parse_value(&mut Lexer::new("Bool(foo)".chars())).is_err());
    }

    #[test]
    fn parse_value_test_13() {
        assert!(parse_value(&mut Lexer::new("I32()".chars())).is_err());
    }

    #[test]
    fn parse_value_test_14() {
        assert!(parse_value(&mut Lexer::new("F32 3.14".chars())).is_err());
    }

    #[test]
    fn parse_register_test_1() {
        let reg = parse_register(&mut Lexer::new("$sp".chars())).unwrap();
        assert_eq!(reg, RegisterName::StackPointer);
    }

    #[test]
    fn parse_register_test_2() {
        let reg = parse_register(&mut Lexer::new("$fp".chars())).unwrap();
        assert_eq!(reg, RegisterName::FramePointer);
    }

    #[test]
    fn parse_register_test_3() {
        let reg = parse_register(&mut Lexer::new("$pc".chars())).unwrap();
        assert_eq!(reg, RegisterName::ProgramCounter);
    }

    #[test]
    fn parse_register_test_4() {
        let reg = parse_register(&mut Lexer::new("$7".chars())).unwrap();
        assert_eq!(reg, RegisterName::R(7));
    }

    #[test]
    fn parse_type_test_1() {
        let t = parse_type(&mut Lexer::new("I32".chars())).unwrap();
        assert_eq!(t, Type::I32);
    }

    #[test]
    fn parse_type_test_2() {
        let t = parse_type(&mut Lexer::new("Bool".chars())).unwrap();
        assert_eq!(t, Type::Bool);
    }

    #[test]
    fn parse_type_test_3() {
        let t = parse_type(&mut Lexer::new("Void".chars())).unwrap();
        assert_eq!(t, Type::Void);
    }

    #[test]
    fn parse_type_test_4() {
        assert!(parse_type(&mut Lexer::new("bar".chars())).is_err());
    }

    #[test]
    fn parser_test_1() {
        let (insts, labels) = parse(Lexer::new("pushc I32(3)".chars())).unwrap();
        assert!(labels.is_empty());
        let mut iter = insts.iter();
        assert_eq!(*iter.next().unwrap(), PUSHC(Value::I32(3)));
        assert!(iter.next().is_none());
    }

    #[test]
    fn parser_test_2() {
        let (insts, labels) = parse(Lexer::new("pushc F32(3.1) pushc F32(4.2) s.add".chars())).unwrap();
        assert!(labels.is_empty());
        let mut iter = insts.iter();
        assert_eq!(*iter.next().unwrap(), PUSHC(Value::F32(3.1)));
        assert_eq!(*iter.next().unwrap(), PUSHC(Value::F32(4.2)));
        assert_eq!(*iter.next().unwrap(), BOp(BinaryOp::ADD, Loc::Stack, Loc::Stack, Loc::Stack));
        assert!(iter.next().is_none());
    }

    #[test]
    fn parsre_test_3() {
        let (insts, labels) = parse(Lexer::new("jump L1 L1: pushc Bool(true)".chars())).unwrap();
        assert_eq!(labels.len(), 1);
        assert!(labels.contains_key("L1"));
        assert_eq!(*labels.get("L1").unwrap(), 1 as usize);
        let mut iter = insts.iter();
        assert_eq!(*iter.next().unwrap(), JUMP("L1".to_string()));
        assert_eq!(*iter.next().unwrap(), PUSHC(Value::Bool(true)));
        assert!(iter.next().is_none());
    }
}
