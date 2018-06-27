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
use lexer;
use lexer::*;
use std::iter::Iterator;
use std::collections::HashMap;
use std::fmt;
use std::error;
use std::result;
use std::convert;

#[derive(Debug,Clone)]
pub enum ParserError<'a> {
    UnexpectedToken,
    UnexpectedIdentifier,
    ExpectingMoreTokens,
    LexerError(lexer::Error<'a>)
}

impl<'a> fmt::Display for ParserError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<'a> error::Error for ParserError<'a> {
    fn description(&self) -> &str {
        use self::ParserError::*;
        match self {
            &UnexpectedToken => "Found an unexpected token while parsing",
            &UnexpectedIdentifier => "Found an unexpected identifier while parsing",
            &ExpectingMoreTokens => "Expecting more tokens but token stream ended",
            LexerError(_) => "Lexing error occured while parsing (see cause)"
        }
    }

    fn cause(&self) -> Option<&error::Error> {
        match self {
            &ParserError::LexerError(ref e) => Some(e),
            _ => None
        }
    }
}

impl<'a> convert::From<lexer::Error<'a>> for ParserError<'a> {
    fn from<'b>(error: lexer::Error<'b>) -> ParserError<'b> {
        ParserError::LexerError(error)
    }
}

impl<'a> convert::From<ParserError<'a>> for String {
    fn from(error: ParserError) -> Self {
        error.to_string()
    }
}

type Result<'a, T> = result::Result<T, ParserError<'a>>;

macro_rules! unexpected_token ( ($t:expr)  => (Err(ParserError::UnexpectedToken)) );
macro_rules! unexpected_id    ( ($id:expr) => (Err(ParserError::UnexpectedIdentifier)) );
macro_rules! unexpected_end   ( ()         => (Err(ParserError::ExpectingMoreTokens)) );

macro_rules! eat_token_ {
    ($iter:expr, $expect:tt) => ({
        let t = $iter.next().transpose()?.ok_or(ParserError::ExpectingMoreTokens)?;
        match t.token {
            Token::$expect => Ok(t.token),
            _ => unexpected_token!(t),
        }
    })
}

macro_rules! eat_token {
    ($iter:expr, $expect:tt) => ({
        let t = $iter.next().transpose()?.ok_or(ParserError::ExpectingMoreTokens)?;
        match t.token {
            Token::$expect(v) => Ok(v),
            _ => unexpected_token!(t),
        }
    })
}

fn parse_value<'a>(lexer: &mut Lexer<'a>) -> Result<'a, Value> {
    macro_rules! parse_as (
        ($id:tt, $val:tt) => ({
            eat_token_!(lexer, LParen)?;
            let v = eat_token!(lexer, $id)?;
            eat_token_!(lexer, RParen)?;
            Ok(Value::$val(v))
        })
    );

    match lexer.next().clone().transpose()?.ok_or(ParserError::ExpectingMoreTokens)?.token {
        Token::Void => Ok(Value::Void),
        Token::Ident(id) => match id.to_lowercase().as_ref() {
            "i32" => parse_as!(Integer, I32),
            "f32" => parse_as!(Float, F32),
            "char" => parse_as!(Char, Char),
            "bool" => parse_as!(Bool, Bool),
            "iptr" => parse_as!(Address, IPtr),
            "sptr" => parse_as!(Address, SPtr),
            _id => return unexpected_id!(_id)
        },
        _t => return unexpected_token!(_t),
    }
}

fn parse_register<'a>(lexer: &mut Lexer<'a>) -> Result<'a, RegisterName> {
    match lexer.next().transpose()?.ok_or(ParserError::ExpectingMoreTokens)?.token {
        Token::SP => Ok(RegisterName::StackPointer),
        Token::FP => Ok(RegisterName::FramePointer),
        Token::PC => Ok(RegisterName::ProgramCounter),
        Token::R(i) => Ok(RegisterName::R(i)),
        _t => unexpected_token!(_t),
    }
}

fn parse_type<'a>(lexer: &mut Lexer<'a>) -> Result<'a, Type> {
    match lexer.next().transpose()?.ok_or(ParserError::ExpectingMoreTokens)?.token {
        Token::Void => Ok(Type::Void),
        Token::Ident(id) => match id.to_lowercase().as_ref() {
            "i32" => Ok(Type::I32),
            "f32" => Ok(Type::F32),
            "char" => Ok(Type::Char),
            "bool" => Ok(Type::Bool),
            "iptr" => Ok(Type::IPtr),
            "sptr" => Ok(Type::SPtr),
            _id => return unexpected_id!(_id),
        }
        _t => return unexpected_token!(_t),
    }
}

type LocParser<'a> = Fn(&mut Lexer<'a>) -> Result<'a, Loc>;

/*
This function acts as a continuation for parsing a register location
in a v-instruction.
*/
fn parse_regloc<'a>(lexer: &mut Lexer<'a>) -> Result<'a, Loc> {
    Ok(Loc::Reg(parse_register(lexer)?))
}

/*
This function is intended to mirror `parse_regloc`, acting as a
continuation for parsing a stack location in a v-instruction.
Since stack locactions are implicit, not tokens are ever
consumed on invocation.
*/
fn parse_stackloc<'a>(_: &mut Lexer<'a>) -> Result<'a, Loc> {
    Ok(Loc::Stack)
}

/*
Helper for parsing an identifier as a v-instruction that takes
one location argument. The identifier is converted to lowercase
and matched against the names of such v-instruction. If a match
is found, the matching instruction is returned, consuming the
tokens necessary to completely parse the instruction. If no
match is found, None is returned and no tokens are consumed.
*/
fn parse_as_vinst1<'a>(ident: &String, lexer: &mut Lexer<'a>, parse_loc: &LocParser<'a>) -> Result<'a, Option<Instruction>> {
    use cookie_base::Instruction::*;
    use cookie_base::Target::*;
    let inst = match ident.to_lowercase().as_ref() {
        "djump" => {
            let loc = parse_loc(lexer)?;
            Some(DJUMP(loc))
        },
        "branchon" => {
            let v = parse_value(lexer)?;
            let loc = parse_loc(lexer)?;
            let l = eat_token!(lexer, Ident)?;
            Some(BRANCHON(v, UnresolvedLabel(l), loc))
        },
        "print" => {
            let loc = parse_loc(lexer)?;
            Some(PRINT(loc))
        },
        "read" => {
            let t = parse_type(lexer)?;
            let loc = parse_loc(lexer)?;
            Some(READ(t, loc))
        },
        _ => None
    };
    Ok(inst)
}

/*
Helper for parsing an identifier as a v-instruction that takes
two location argument.
*/
fn parse_as_vinst2<'a>(ident: &String, lexer: &mut Lexer<'a>, parse_loc1: &LocParser<'a>, parse_loc2: &LocParser<'a>) -> Result<'a, Option<Instruction>> {
    use cookie_base::Instruction::*;
    use cookie_base::UnaryOp::*;

    macro_rules! gen_uop {
        ($op:ident) => ({
            let loc1 = parse_loc1(lexer)?;
            let loc2 = parse_loc2(lexer)?;
            Some(UOp($op, loc1, loc2))
        })
    }

    let inst = match ident.to_lowercase().as_ref() {
        "neg" => gen_uop!(NEG),
        "not" => gen_uop!(NOT),
        "cvt" => {
            let t = parse_type(lexer)?;
            let loc1 = parse_loc1(lexer)?;
            let loc2 = parse_loc2(lexer)?;
            Some(UOp(CVT(t), loc1, loc2))
        }
        "loadfrom" => {
            let loc1 = parse_loc1(lexer)?;
            let loc2 = parse_loc2(lexer)?;
            Some(LOADFROM(loc1, loc2))
        },
        "storeto" => {
            let loc1 = parse_loc1(lexer)?;
            let loc2 = parse_loc2(lexer)?;
            Some(STORETO(loc1, loc2))
        },
        _ => None
    };
    Ok(inst)
}

/*
Helper for parsing an identifier as a v-instruction that takes
three location arguments.
*/
fn parse_as_vinst3<'a>(ident: &String, lexer: &mut Lexer<'a>, parse_loc1: &LocParser<'a>, parse_loc2: &LocParser<'a>, parse_loc3: &LocParser<'a>) -> Result<'a, Option<Instruction>> {
    use cookie_base::Instruction::*;
    use cookie_base::BinaryOp::*;

    macro_rules! gen_bop {
        ($op:ident) => ({
            let loc1 = parse_loc1(lexer)?;
            let loc2 = parse_loc2(lexer)?;
            let loc3 = parse_loc3(lexer)?;
            Some(BOp($op, loc1, loc2, loc3))
        })
    }

    let inst = match ident.to_lowercase().as_ref() {
        "add" => gen_bop!(ADD),
        "sub" => gen_bop!(SUB),
        "mul" => gen_bop!(MUL),
        "div" => gen_bop!(DIV),
        "mod" => gen_bop!(MOD),
        "eq" => gen_bop!(EQ),
        "lt" => gen_bop!(LT),
        "le" => gen_bop!(LE),
        "gt" => gen_bop!(GT),
        "ge" => gen_bop!(GE),
        "and" => gen_bop!(AND),
        "or" => gen_bop!(OR),
        "xor" => gen_bop!(XOR),
        _ => None
    };
    Ok(inst)
}

fn parse_vinst<'a>(lexer: &mut Lexer<'a>, parse_loc: &LocParser<'a>) -> Result<'a, Instruction> {
    let id = eat_token!(lexer, Ident)?;
    parse_as_vinst1(&id, lexer, parse_loc).transpose()
        .or_else(|| parse_as_vinst2(&id, lexer, parse_loc, parse_loc).transpose())
        .or_else(|| parse_as_vinst3(&id, lexer, parse_loc, parse_loc, parse_loc).transpose())
        .unwrap_or(unexpected_id!(id))
}

fn resolve_label(inst: &Instruction, labels: &LabelTable) -> Instruction {
    use cookie_base::Instruction::*;
    use cookie_base::Target::*;
    match inst {
        JUMP(UnresolvedLabel(l)) => { 
            if let Some(n) = labels.get(&l.to_string()) { JUMP(InternalLabel(*n, l.to_string())) } 
            else { inst.clone() }
        }
        BRANCHON(v, UnresolvedLabel(l), c) => {
            if let Some(n) = labels.get(&l.to_string()) { BRANCHON(*v, InternalLabel(*n, l.to_string()), *c) } 
            else { inst.clone() }
        }
        _ => inst.clone()
    }
}

pub fn parse<'a>(mut lexer: Lexer<'a>) -> Result<(InstructionList, LabelTable)> {
    use cookie_base::Instruction::*;
    use cookie_base::Target::*;
    let mut insts: Vec<Instruction> = Vec::new();
    let mut labels: LabelTable = HashMap::new();

    loop {
        match lexer.next().transpose()?.map(|t| t.token) {
            Some(Token::Ident(id)) => match id.to_lowercase().as_ref() {
                "s" => {
                    eat_token_!(lexer, Dot)?;
                    let inst = parse_vinst(&mut lexer, &parse_stackloc)?;
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
                "jump" => { let l = eat_token!(lexer, Ident)?; insts.push(JUMP(UnresolvedLabel(l))); },
                "exit" => { insts.push(EXIT); }
                id => return unexpected_id!(id)
            },
            Some(Token::Label(l)) => { labels.insert(l.to_string(), insts.len()); },
            Some(_t) => return unexpected_token!(_t),
            None => break,
        };
    }

    let insts = insts.iter_mut().map(|i| resolve_label(i, &labels)).collect::<InstructionList>();

    return Ok((insts, labels));
}

#[cfg(test)]
mod test {
    use super::*;
    use cookie_base::Instruction::*;
    use cookie_base::Target::*;

    #[test]
    fn parse_vinst_test_1() {
        let inst = parse_vinst(&mut Lexer::new("Add"), &parse_stackloc).unwrap();
        assert_eq!(inst, Instruction::BOp(BinaryOp::ADD, Loc::Stack, Loc::Stack, Loc::Stack));
    }

    #[test]
    fn parse_vinst_test_2() {
        let inst = parse_vinst(&mut Lexer::new("EQ"), &parse_stackloc).unwrap();
        assert_eq!(inst, Instruction::BOp(BinaryOp::EQ, Loc::Stack, Loc::Stack, Loc::Stack));
    }

    #[test]
    fn parse_vinst_test_3() {
        let inst = parse_vinst(&mut Lexer::new("NOT"), &parse_stackloc).unwrap();
        assert_eq!(inst, Instruction::UOp(UnaryOp::NOT, Loc::Stack, Loc::Stack));
    }

    #[test]
    fn parse_vinst_test_4() {
        assert!(parse_vinst(&mut Lexer::new("foo"), &parse_stackloc).is_err());
    }

    #[test]
    fn parse_vinst_test_5() {
        let inst = parse_vinst(&mut Lexer::new("CVT F32"), &parse_stackloc).unwrap();
        assert_eq!(inst, Instruction::UOp(UnaryOp::CVT(Type::F32), Loc::Stack, Loc::Stack));
    }

    #[test]
    fn parse_value_test_1() {
        let val = parse_value(&mut Lexer::new("I32(3)")).unwrap();
        assert_eq!(val, Value::I32(3));
    }

    #[test]
    fn parse_value_test_2() {
        let val = parse_value(&mut Lexer::new("F32(2.71828)")).unwrap();
        assert_eq!(val, Value::F32(2.71828));
    }

    #[test]
    fn parse_value_test_3() {
        let val = parse_value(&mut Lexer::new(r"Char('\\')")).unwrap();
        assert_eq!(val, Value::Char('\\'));
    }

    #[test]
    fn parse_value_test_4() {
        let val = parse_value(&mut Lexer::new("Bool(False)")).unwrap();
        assert_eq!(val, Value::Bool(false));
    }

    #[test]
    fn parse_value_test_5() {
        let val = parse_value(&mut Lexer::new("IPtr(0xabc)")).unwrap();
        assert_eq!(val, Value::IPtr(0xabc));
    }

    #[test]
    fn parse_value_test_6() {
        let val = parse_value(&mut Lexer::new("SPtr(0x123)")).unwrap();
        assert_eq!(val, Value::SPtr(0x123));
    }

    #[test]
    fn parse_value_test_7() {
        let val = parse_value(&mut Lexer::new("Void")).unwrap();
        assert_eq!(val, Value::Void);
    }

    #[test]
    fn parse_value_test_8() {
        assert!(parse_value(&mut Lexer::new("foo")).is_err());
    }

    #[test]
    fn parse_value_test_9() {
        assert!(parse_value(&mut Lexer::new("I32(2.0)")).is_err());
    }

    #[test]
    fn parse_value_test_10() {
        assert!(parse_value(&mut Lexer::new("F32(4)")).is_err());
    }

    #[test]
    fn parse_value_test_11() {
        assert!(parse_value(&mut Lexer::new("Char(c)")).is_err());
    }

    #[test]
    fn parse_value_test_12() {
        assert!(parse_value(&mut Lexer::new("Bool(foo)")).is_err());
    }

    #[test]
    fn parse_value_test_13() {
        assert!(parse_value(&mut Lexer::new("I32()")).is_err());
    }

    #[test]
    fn parse_value_test_14() {
        assert!(parse_value(&mut Lexer::new("F32 3.14")).is_err());
    }

    #[test]
    fn parse_register_test_1() {
        let reg = parse_register(&mut Lexer::new("$sp")).unwrap();
        assert_eq!(reg, RegisterName::StackPointer);
    }

    #[test]
    fn parse_register_test_2() {
        let reg = parse_register(&mut Lexer::new("$fp")).unwrap();
        assert_eq!(reg, RegisterName::FramePointer);
    }

    #[test]
    fn parse_register_test_3() {
        let reg = parse_register(&mut Lexer::new("$pc")).unwrap();
        assert_eq!(reg, RegisterName::ProgramCounter);
    }

    #[test]
    fn parse_register_test_4() {
        let reg = parse_register(&mut Lexer::new("$7")).unwrap();
        assert_eq!(reg, RegisterName::R(7));
    }

    #[test]
    fn parse_type_test_1() {
        let t = parse_type(&mut Lexer::new("I32")).unwrap();
        assert_eq!(t, Type::I32);
    }

    #[test]
    fn parse_type_test_2() {
        let t = parse_type(&mut Lexer::new("Bool")).unwrap();
        assert_eq!(t, Type::Bool);
    }

    #[test]
    fn parse_type_test_3() {
        let t = parse_type(&mut Lexer::new("Void")).unwrap();
        assert_eq!(t, Type::Void);
    }

    #[test]
    fn parse_type_test_4() {
        assert!(parse_type(&mut Lexer::new("bar")).is_err());
    }

    #[test]
    fn parser_test_1() {
        let (insts, labels) = parse(Lexer::new("pushc I32(3)")).unwrap();
        assert!(labels.is_empty());
        let mut iter = insts.iter();
        assert_eq!(*iter.next().unwrap(), PUSHC(Value::I32(3)));
        assert!(iter.next().is_none());
    }

    #[test]
    fn parser_test_2() {
        let (insts, labels) = parse(Lexer::new("pushc F32(3.1) pushc F32(4.2) s.add")).unwrap();
        assert!(labels.is_empty());
        let mut iter = insts.iter();
        assert_eq!(*iter.next().unwrap(), PUSHC(Value::F32(3.1)));
        assert_eq!(*iter.next().unwrap(), PUSHC(Value::F32(4.2)));
        assert_eq!(*iter.next().unwrap(), BOp(BinaryOp::ADD, Loc::Stack, Loc::Stack, Loc::Stack));
        assert!(iter.next().is_none());
    }

    #[test]
    fn parsre_test_3() {
        let (insts, labels) = parse(Lexer::new("jump L1 L1: pushc Bool(true)")).unwrap();
        assert_eq!(labels.len(), 1);
        assert!(labels.contains_key("L1"));
        assert_eq!(*labels.get("L1").unwrap(), 1 as usize);
        let mut iter = insts.iter();
        assert_eq!(*iter.next().unwrap(), JUMP(InternalLabel(1, "L1".to_string())));
        assert_eq!(*iter.next().unwrap(), PUSHC(Value::Bool(true)));
        assert!(iter.next().is_none());
    }
}
