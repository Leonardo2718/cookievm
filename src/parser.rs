/*

Copyright (C) 2018, 2019 Leonardo Banderali

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

use instruction::*;
use lexer;
use lexer::*;
use std::collections::HashMap;
use std::convert;
use std::error;
use std::fmt;
use std::iter::Iterator;
use std::result;

#[derive(Debug, Clone)]
pub enum ParserError<'a> {
    UnexpectedToken(Token),
    UnexpectedIdentifier(String),
    ExpectingMoreTokens,
    LexerError(lexer::Error<'a>),
}

#[derive(Debug, Clone)]
pub struct Error<'a> {
    pub error: ParserError<'a>,
    pub position: Position<'a>,
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
            &UnexpectedToken(_) => "Found an unexpected token while parsing",
            &UnexpectedIdentifier(_) => "Found an unexpected identifier while parsing",
            &ExpectingMoreTokens => "Expecting more tokens but token stream ended",
            LexerError(_) => "Lexing error occured while parsing (see cause)",
        }
    }

    fn cause(&self) -> Option<&error::Error> {
        match self {
            &ParserError::LexerError(ref e) => Some(e),
            _ => None,
        }
    }
}

impl<'a> convert::From<ParserError<'a>> for Error<'a> {
    fn from<'b>(error: ParserError<'b>) -> Error<'b> {
        Error {
            error,
            position: Position {
                source: "",
                position: 0,
                line: 0,
                column: 0,
            },
        }
    }
}

impl<'a> convert::From<lexer::Error<'a>> for Error<'a> {
    fn from<'b>(error: lexer::Error<'b>) -> Error<'b> {
        Error {
            error: ParserError::LexerError(error),
            position: Position {
                source: "",
                position: 0,
                line: 0,
                column: 0,
            },
        }
    }
}

impl<'a> convert::From<ParserError<'a>> for String {
    fn from(error: ParserError) -> Self {
        error.to_string()
    }
}

type Result<'a, T> = result::Result<T, Error<'a>>;

macro_rules! unexpected_token ( ($t:expr)  => ( Err(Error{error: ParserError::UnexpectedToken($t.token), position:$t.pos})) );
macro_rules! unexpected_id    ( ($id:expr,$p:expr) => ( Err(Error{error: ParserError::UnexpectedIdentifier($id), position: $p})) );

macro_rules! eat_token_ {
    ($iter:expr, $expect:tt) => {{
        let t = $iter
            .next()
            .transpose()?
            .ok_or(ParserError::ExpectingMoreTokens)?;
        match t.token {
            Token::$expect => Ok(t.token),
            _ => unexpected_token!(t),
        }
    }};
}

macro_rules! eat_token {
    ($iter:expr, $expect:tt) => {{
        let t = $iter
            .next()
            .transpose()?
            .ok_or(ParserError::ExpectingMoreTokens)?;
        match t.token {
            Token::$expect(v) => Ok(v),
            _ => unexpected_token!(t),
        }
    }};
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

    let t = lexer
        .next()
        .clone()
        .transpose()?
        .ok_or(ParserError::ExpectingMoreTokens)?;
    match t.token {
        Token::Void => Ok(Value::Void),
        Token::Ident(id) => match id.to_lowercase().as_ref() {
            "i32" => parse_as!(Integer, I32),
            "f32" => parse_as!(Float, F32),
            "char" => parse_as!(Char, Char),
            "bool" => parse_as!(Bool, Bool),
            "iptr" => parse_as!(Address, IPtr),
            "sptr" => parse_as!(Address, SPtr),
            _id => return unexpected_id!(_id.to_string(), t.pos),
        },
        _ => return unexpected_token!(t),
    }
}

fn parse_register<'a>(lexer: &mut Lexer<'a>) -> Result<'a, RegisterName> {
    let t = lexer.next().clone();
    let t = t.transpose()?.ok_or(ParserError::ExpectingMoreTokens)?;
    match t.token {
        Token::SP => Ok(RegisterName::StackPointer),
        Token::FP => Ok(RegisterName::FramePointer),
        Token::PC => Ok(RegisterName::ProgramCounter),
        Token::R(i) => Ok(RegisterName::R(i)),
        _ => unexpected_token!(t),
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

    let t = lexer
        .next()
        .clone()
        .transpose()?
        .ok_or(ParserError::ExpectingMoreTokens)?;
    match t.token {
        Token::Void => Ok(Source::Immediate(Value::Void)),
        Token::Ident(id) => match id.to_lowercase().as_ref() {
            "i32" => parse_as_value!(Integer, I32),
            "f32" => parse_as_value!(Float, F32),
            "char" => parse_as_value!(Char, Char),
            "bool" => parse_as_value!(Bool, Bool),
            "iptr" => parse_as_value!(Address, IPtr),
            "sptr" => parse_as_value!(Address, SPtr),
            id => return unexpected_id!(id.to_string(), t.pos),
        },
        Token::SP => parse_as_register!(RegisterName::StackPointer),
        Token::FP => parse_as_register!(RegisterName::FramePointer),
        Token::PC => parse_as_register!(RegisterName::ProgramCounter),
        Token::R(i) => parse_as_register!(RegisterName::R(i)),
        Token::StackPos(p) => Ok(Source::Stack(p)),
        _ => return unexpected_token!(t),
    }
}

fn parse_destination<'a>(lexer: &mut Lexer<'a>) -> Result<'a, Destination> {
    macro_rules! parse_as_register (
        ($reg:expr) => (Ok(Destination::Register($reg)))
    );

    let t = lexer
        .next()
        .clone()
        .transpose()?
        .ok_or(ParserError::ExpectingMoreTokens)?;
    match t.token {
        Token::SP => parse_as_register!(RegisterName::StackPointer),
        Token::FP => parse_as_register!(RegisterName::FramePointer),
        Token::PC => parse_as_register!(RegisterName::ProgramCounter),
        Token::R(i) => parse_as_register!(RegisterName::R(i)),
        Token::StackPos(p) => Ok(Destination::Stack(p)),
        _ => return unexpected_token!(t),
    }
}

fn parse_type<'a>(lexer: &mut Lexer<'a>) -> Result<'a, Type> {
    let t = lexer
        .next()
        .clone()
        .transpose()?
        .ok_or(ParserError::ExpectingMoreTokens)?;
    match t.token {
        Token::Void => Ok(Type::Void),
        Token::Ident(id) => match id.to_lowercase().as_ref() {
            "i32" => Ok(Type::I32),
            "f32" => Ok(Type::F32),
            "char" => Ok(Type::Char),
            "bool" => Ok(Type::Bool),
            "iptr" => Ok(Type::IPtr),
            "sptr" => Ok(Type::SPtr),
            id => return unexpected_id!(id.to_string(), t.pos),
        },
        _ => return unexpected_token!(t),
    }
}

fn parse_s<'a>(lexer: &mut Lexer<'a>) -> Result<'a, Source> {
    let mut peekable = lexer.clone().peekable();
    let peeked = peekable.peek().ok_or(ParserError::ExpectingMoreTokens)?;
    match peeked.clone()?.token {
        Token::ExclamationMark => {
            lexer.next();
            Ok(Source::Stack(0))
        }
        Token::QuestionMark => {
            lexer.next();
            Ok(Source::Stack(0))
        }
        _ => {
            let src = parse_source(lexer)?;
            Ok(src)
        }
    }
}

fn parse_d<'a>(lexer: &mut Lexer<'a>) -> Result<'a, Destination> {
    let mut peekable = lexer.clone().peekable();
    let peeked = peekable.peek().ok_or(ParserError::ExpectingMoreTokens)?;
    match peeked.clone()?.token {
        Token::ExclamationMark => {
            lexer.next();
            Ok(Destination::Stack(0))
        }
        Token::QuestionMark => {
            lexer.next();
            Ok(Destination::Stack(0))
        }
        _ => {
            let dest = parse_destination(lexer)?;
            Ok(dest)
        }
    }
}

fn parse_ss<'a>(lexer: &mut Lexer<'a>) -> Result<'a, (Source, Source)> {
    let mut peekable = lexer.clone().peekable();
    let peeked = peekable.peek().ok_or(ParserError::ExpectingMoreTokens)?;
    match peeked.clone()?.token {
        Token::ExclamationMark => {
            lexer.next();
            Ok((Source::Stack(1), Source::Stack(0)))
        }
        Token::QuestionMark => {
            lexer.next();
            Ok((Source::Stack(0), Source::Stack(1)))
        }
        _ => {
            let src1 = parse_source(lexer)?;
            let src2 = parse_source(lexer)?;
            Ok((src1, src2))
        }
    }
}

fn parse_sss<'a>(lexer: &mut Lexer<'a>) -> Result<'a, (Source, Source, Source)> {
    let mut peekable = lexer.clone().peekable();
    let peeked = peekable.peek().ok_or(ParserError::ExpectingMoreTokens)?;
    match peeked.clone()?.token {
        Token::ExclamationMark => {
            lexer.next();
            Ok((Source::Stack(2), Source::Stack(1), Source::Stack(0)))
        }
        Token::QuestionMark => {
            lexer.next();
            Ok((Source::Stack(0), Source::Stack(1), Source::Stack(2)))
        }
        _ => {
            let src1 = parse_source(lexer)?;
            let src2 = parse_source(lexer)?;
            let src3 = parse_source(lexer)?;
            Ok((src1, src2, src3))
        }
    }
}

fn parse_ds<'a>(lexer: &mut Lexer<'a>) -> Result<'a, (Destination, Source)> {
    let mut peekable = lexer.clone().peekable();
    let peeked = peekable.peek().ok_or(ParserError::ExpectingMoreTokens)?;
    match peeked.clone()?.token {
        Token::ExclamationMark => {
            lexer.next();
            Ok((Destination::Stack(0), Source::Stack(0)))
        }
        Token::QuestionMark => {
            lexer.next();
            Ok((Destination::Stack(0), Source::Stack(0)))
        }
        _ => {
            let dest = parse_destination(lexer)?;
            let src = parse_source(lexer)?;
            Ok((dest, src))
        }
    }
}

fn parse_dss<'a>(lexer: &mut Lexer<'a>) -> Result<'a, (Destination, Source, Source)> {
    let mut peekable = lexer.clone().peekable();
    let peeked = peekable.peek().ok_or(ParserError::ExpectingMoreTokens)?;
    match peeked.clone()?.token {
        Token::ExclamationMark => {
            lexer.next();
            Ok((Destination::Stack(0), Source::Stack(1), Source::Stack(0)))
        }
        Token::QuestionMark => {
            lexer.next();
            Ok((Destination::Stack(0), Source::Stack(0), Source::Stack(1)))
        }
        _ => {
            let dest = parse_destination(lexer)?;
            let src1 = parse_source(lexer)?;
            let src2 = parse_source(lexer)?;
            Ok((dest, src1, src2))
        }
    }
}

pub fn parse<'a>(mut lexer: Lexer<'a>) -> Result<InstructionList> {
    use instruction::BinaryOp::*;
    use instruction::Instruction::*;
    use instruction::Target::*;
    use instruction::UnaryOp::*;
    let mut insts: Vec<Instruction> = Vec::new();
    let mut symbols: SymbolTable = HashMap::new();

    macro_rules! push_bop {
        ($op:ident) => {{
            let (dest, src1, src2) = parse_dss(&mut lexer)?;
            insts.push(BOp($op, dest, src1, src2));
        }};
    }

    macro_rules! push_uop {
        ($op:ident) => {{
            let (dest, src) = parse_ds(&mut lexer)?;
            insts.push(UOp($op, dest, src));
        }};
    }

    loop {
        let t = lexer.next().transpose()?;
        match t.clone().map(|t| t.token) {
            Some(Token::Ident(id)) => match id.to_lowercase().as_ref() {
                "add" => push_bop!(ADD),
                "sub" => push_bop!(SUB),
                "mul" => push_bop!(MUL),
                "div" => push_bop!(DIV),
                "mod" => push_bop!(MOD),
                "and" => push_bop!(AND),
                "or" => push_bop!(OR),
                "eq" => push_bop!(EQ),
                "lt" => push_bop!(LT),
                "le" => push_bop!(LE),
                "gt" => push_bop!(GT),
                "ge" => push_bop!(GE),
                "xor" => push_bop!(XOR),
                "neg" => push_uop!(NEG),
                "not" => push_uop!(NOT),
                "cvt" => {
                    let t = parse_type(&mut lexer)?;
                    let (dest, src) = parse_ds(&mut lexer)?;
                    insts.push(UOp(CVT(t), dest, src));
                }
                "loadfrom" => {
                    let (dest, src) = parse_ds(&mut lexer)?;
                    insts.push(LOADFROM(dest, src));
                }
                "storeto" => {
                    let (src1, src2) = parse_ss(&mut lexer)?;
                    insts.push(STORETO(src1, src2));
                }
                "djump" => {
                    let src = parse_source(&mut lexer)?;
                    insts.push(DJUMP(src));
                }
                "branch" => {
                    let src = parse_s(&mut lexer)?;
                    let l = eat_token!(lexer, Ident)?;
                    insts.push(BRANCH(src, UnresolvedSymbol(l)));
                }
                "dbranch" => {
                    let (src1, src2) = parse_ss(&mut lexer)?;
                    insts.push(DBRANCH(src1, src2));
                }
                "print" => {
                    let src = parse_s(&mut lexer)?;
                    insts.push(PRINT(src));
                }
                "read" => {
                    let t = parse_type(&mut lexer)?;
                    let dest = parse_d(&mut lexer)?;
                    insts.push(READ(t, dest));
                }
                "pushc" => {
                    let val = parse_value(&mut lexer)?;
                    insts.push(PUSHC(val));
                }
                "pushr" => {
                    let reg = parse_register(&mut lexer)?;
                    insts.push(PUSHR(reg));
                }
                "popr" => {
                    let reg = parse_register(&mut lexer)?;
                    insts.push(POPR(reg));
                }
                "pop" => {
                    insts.push(POP);
                }
                "jump" => {
                    let l = eat_token!(lexer, Ident)?;
                    insts.push(JUMP(UnresolvedSymbol(l)));
                }
                "exit" => {
                    insts.push(EXIT);
                }
                id => return unexpected_id!(id.to_string(), t.unwrap().pos),
            },
            Some(Token::Label(l)) => {
                symbols.insert(l.to_string(), insts.len());
            }
            Some(_) => return unexpected_token!(t.clone().unwrap()),
            None => break,
        };
    }

    let insts = resolve_internal_lables(insts, &symbols);

    return Ok(insts);
}

#[cfg(test)]
mod test {
    use super::*;
    use instruction::Instruction::*;
    use instruction::Target::*;

    #[test]
    fn parse_dss_test_1() {
        let insts = parse(Lexer::new("Add @0 @1 @0")).unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(
            insts[0],
            Instruction::BOp(
                BinaryOp::ADD,
                Destination::Stack(0),
                Source::Stack(1),
                Source::Stack(0)
            )
        );
    }

    #[test]
    fn parse_dss_test_2() {
        let insts = parse(Lexer::new("EQ @0 @1 @0")).unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(
            insts[0],
            Instruction::BOp(
                BinaryOp::EQ,
                Destination::Stack(0),
                Source::Stack(1),
                Source::Stack(0)
            )
        );
    }

    #[test]
    fn parse_dss_test_3() {
        let insts = parse(Lexer::new("sub !")).unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(
            insts[0],
            Instruction::BOp(
                BinaryOp::SUB,
                Destination::Stack(0),
                Source::Stack(1),
                Source::Stack(0)
            )
        );
    }

    #[test]
    fn parse_dss_test_4() {
        let insts = parse(Lexer::new("mUl ?")).unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(
            insts[0],
            Instruction::BOp(
                BinaryOp::MUL,
                Destination::Stack(0),
                Source::Stack(0),
                Source::Stack(1)
            )
        );
    }

    #[test]
    fn parse_ds_test_1() {
        let insts = parse(Lexer::new("NOT @0 @0")).unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(
            insts[0],
            Instruction::UOp(UnaryOp::NOT, Destination::Stack(0), Source::Stack(0))
        );
    }

    #[test]
    fn parse_ds_test_2() {
        let insts = parse(Lexer::new("CVT F32 @0 @0")).unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(
            insts[0],
            Instruction::UOp(
                UnaryOp::CVT(Type::F32),
                Destination::Stack(0),
                Source::Stack(0)
            )
        );
    }

    #[test]
    fn parse_ds_test_3() {
        let insts = parse(Lexer::new("LoadFrom !")).unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(
            insts[0],
            Instruction::LOADFROM(Destination::Stack(0), Source::Stack(0))
        );
    }

    #[test]
    fn parse_ds_test_4() {
        let insts = parse(Lexer::new("CVT F32 ?")).unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(
            insts[0],
            Instruction::UOp(
                UnaryOp::CVT(Type::F32),
                Destination::Stack(0),
                Source::Stack(0)
            )
        );
    }

    #[test]
    fn parse_ss_test_1() {
        let insts = parse(Lexer::new("StoreTo @1 @0")).unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(
            insts[0],
            Instruction::STORETO(Source::Stack(1), Source::Stack(0))
        )
    }

    #[test]
    fn parse_ss_test_2() {
        let insts = parse(Lexer::new("StoreTo !")).unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(
            insts[0],
            Instruction::STORETO(Source::Stack(1), Source::Stack(0))
        )
    }

    #[test]
    fn parse_ss_test_3() {
        let insts = parse(Lexer::new("StoreTo ?")).unwrap();
        assert_eq!(insts.len(), 1);
        assert_eq!(
            insts[0],
            Instruction::STORETO(Source::Stack(0), Source::Stack(1))
        )
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
        assert_eq!(
            *iter.next().unwrap(),
            BOp(
                BinaryOp::ADD,
                Destination::Stack(0),
                Source::Stack(1),
                Source::Stack(0)
            )
        );
        assert!(iter.next().is_none());
    }

    #[test]
    fn parsre_test_3() {
        let insts = parse(Lexer::new("jump L1 L1: pushc Bool(true)")).unwrap();
        let mut iter = insts.iter();
        assert_eq!(
            *iter.next().unwrap(),
            JUMP(LocalSymbol(1, "L1".to_string()))
        );
        assert_eq!(*iter.next().unwrap(), PUSHC(Value::Bool(true)));
        assert!(iter.next().is_none());
    }

    #[test]
    fn parse_test_4() {
        assert!(parse(Lexer::new("foo")).is_err());
    }
}
