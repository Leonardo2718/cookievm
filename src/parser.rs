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

fn parse_source<'a>(lexer: &mut Lexer<'a>) -> Result<'a, Source> {
    macro_rules! parse_as_value (
        ($id:tt, $val:tt) => ({
            eat_token_!(lexer, LParen)?;
            let v = eat_token!(lexer, $id)?;
            eat_token_!(lexer, RParen)?;
            Ok(Source::Immediate(Value::$val(v)))
        })
    );

    macro_rules! parse_as_register (
        ($reg:expr) => (Ok(Source::Register($reg)))
    );

    match lexer.next().clone().transpose()?.ok_or(ParserError::ExpectingMoreTokens)?.token {
        Token::Void => Ok(Source::Immediate(Value::Void)),
        Token::Ident(id) => match id.to_lowercase().as_ref() {
            "i32" => parse_as_value!(Integer, I32),
            "f32" => parse_as_value!(Float, F32),
            "char" => parse_as_value!(Char, Char),
            "bool" => parse_as_value!(Bool, Bool),
            "iptr" => parse_as_value!(Address, IPtr),
            "sptr" => parse_as_value!(Address, SPtr),
            _id => return unexpected_id!(_id)
        },
        Token::SP => parse_as_register!(RegisterName::StackPointer),
        Token::FP => parse_as_register!(RegisterName::FramePointer),
        Token::PC => parse_as_register!(RegisterName::ProgramCounter),
        Token::R(i) => parse_as_register!(RegisterName::R(i)),
        Token::StackPos(p) => Ok(Source::Stack(p)),
        _t => return unexpected_token!(_t),
    }
}

fn parse_destination<'a>(lexer: &mut Lexer<'a>) -> Result<'a, Destination> {
    macro_rules! parse_as_register (
        ($reg:expr) => (Ok(Destination::Register($reg)))
    );

    match lexer.next().clone().transpose()?.ok_or(ParserError::ExpectingMoreTokens)?.token {
        Token::SP => parse_as_register!(RegisterName::StackPointer),
        Token::FP => parse_as_register!(RegisterName::FramePointer),
        Token::PC => parse_as_register!(RegisterName::ProgramCounter),
        Token::R(i) => parse_as_register!(RegisterName::R(i)),
        Token::StackPos(p) => Ok(Destination::Stack(p)),
        _t => return unexpected_token!(_t),
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

pub fn parse<'a>(mut lexer: Lexer<'a>) -> Result<InstructionList> {
    use cookie_base::Instruction::*;
    use cookie_base::BinaryOp::*;
    use cookie_base::UnaryOp::*;
    use cookie_base::Target::*;
    let mut insts: Vec<Instruction> = Vec::new();
    let mut symbols: SymbolTable = HashMap::new();

    macro_rules! push_bop {
        ($op:ident) => ({
            let dest = parse_destination(&mut lexer)?;
            let src1 = parse_source(&mut lexer)?;
            let src2 = parse_source(&mut lexer)?;
            insts.push(BOp($op, dest, src1, src2));
        })
    }

    macro_rules! push_uop {
        ($op:ident) => ({
            let dest = parse_destination(&mut lexer)?;
            let src = parse_source(&mut lexer)?;
            insts.push(UOp($op, dest, src));
        })
    }

    loop {
        match lexer.next().transpose()?.map(|t| t.token) {
            Some(Token::Ident(id)) => match id.to_lowercase().as_ref() {
                "add" => push_bop!(ADD),
                "sub" => push_bop!(SUB),
                "mul" => push_bop!(MUL),
                "div" => push_bop!(DIV),
                "mod" => push_bop!(MOD),
                "eq" => push_bop!(EQ),
                "lt" => push_bop!(LT),
                "le" => push_bop!(LE),
                "gt" => push_bop!(GT),
                "ge" => push_bop!(GE),
                "and" => push_bop!(AND),
                "or" => push_bop!(OR),
                "xor" => push_bop!(XOR),
                "neg" => push_uop!(NEG),
                "not" => push_uop!(NOT),
                "cvt" => {
                    let t = parse_type(&mut lexer)?;
                    let dest = parse_destination(&mut lexer)?;
                    let src = parse_source(&mut lexer)?;
                    insts.push(UOp(CVT(t), dest, src));
                }
                "loadfrom" => {
                    let dest = parse_destination(&mut lexer)?;
                    let src = parse_source(&mut lexer)?;
                    insts.push(LOADFROM(dest, src));
                },
                "storeto" => {
                    let dest = parse_source(&mut lexer)?;
                    let src = parse_source(&mut lexer)?;
                    insts.push(STORETO(dest, src));
                },
                "djump" => {
                    let src = parse_source(&mut lexer)?;
                    insts.push(DJUMP(src));
                },
                "branchon" => {
                    let v = parse_value(&mut lexer)?;
                    let src = parse_source(&mut lexer)?;
                    let l = eat_token!(lexer, Ident)?;
                    insts.push(BRANCHON(v, UnresolvedSymbol(l), src));
                },
                "print" => {
                    let src = parse_source(&mut lexer)?;
                    insts.push(PRINT(src));
                },
                "read" => {
                    let t = parse_type(&mut lexer)?;
                    let dest = parse_destination(&mut lexer)?;
                    insts.push(READ(t, dest));
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
                "jump" => { let l = eat_token!(lexer, Ident)?; insts.push(JUMP(UnresolvedSymbol(l))); },
                "exit" => { insts.push(EXIT); }
                _ => return unexpected_id!(id)
            },
            Some(Token::Label(l)) => { symbols.insert(l.to_string(), insts.len()); },
            Some(_t) => return unexpected_token!(_t),
            None => break,
        };
    }

    let insts = resolve_internal_lables(insts, &symbols);

    return Ok(insts);
}

#[cfg(test)]
mod test {
    use super::*;
    use cookie_base::Instruction::*;
    use cookie_base::Target::*;

    #[test]
    fn parse_vinst_test_1() {
        let insts = parse(Lexer::new("Add @0 @1 @0")).unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(insts[0], Instruction::BOp(BinaryOp::ADD,
                                          Destination::Stack(0), 
                                          Source::Stack(1), 
                                          Source::Stack(0)));
    }

    #[test]
    fn parse_vinst_test_2() {
        let insts = parse(Lexer::new("EQ @0 @1 @0")).unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(insts[0], Instruction::BOp(BinaryOp::EQ,
                                          Destination::Stack(0), 
                                          Source::Stack(1), 
                                          Source::Stack(0)));
    }

    #[test]
    fn parse_vinst_test_3() {
        let insts = parse(Lexer::new("NOT @0 @0")).unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(insts[0], Instruction::UOp(UnaryOp::NOT, Destination::Stack(0), Source::Stack(0)));
    }

    #[test]
    fn parse_vinst_test_4() {
        assert!(parse(Lexer::new("foo")).is_err());
    }

    #[test]
    fn parse_vinst_test_5() {
        let insts = parse(Lexer::new("CVT F32 @0 @0")).unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(insts[0], Instruction::UOp(UnaryOp::CVT(Type::F32), Destination::Stack(0), Source::Stack(0)));
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
        let insts = parse(Lexer::new("pushc I32(3)")).unwrap();
        let mut iter = insts.iter();
        assert_eq!(*iter.next().unwrap(), PUSHC(Value::I32(3)));
        assert!(iter.next().is_none());
    }

    #[test]
    fn parser_test_2() {
        let insts = parse(Lexer::new("pushc F32(3.1) pushc F32(4.2) add @0 @1 @0")).unwrap();
        let mut iter = insts.iter();
        assert_eq!(*iter.next().unwrap(), PUSHC(Value::F32(3.1)));
        assert_eq!(*iter.next().unwrap(), PUSHC(Value::F32(4.2)));
        assert_eq!(*iter.next().unwrap(), BOp(BinaryOp::ADD, Destination::Stack(0), Source::Stack(1), Source::Stack(0)));
        assert!(iter.next().is_none());
    }

    #[test]
    fn parsre_test_3() {
        let insts = parse(Lexer::new("jump L1 L1: pushc Bool(true)")).unwrap();
        let mut iter = insts.iter();
        assert_eq!(*iter.next().unwrap(), JUMP(LocalSymbol(1, "L1".to_string())));
        assert_eq!(*iter.next().unwrap(), PUSHC(Value::Bool(true)));
        assert!(iter.next().is_none());
    }
}
