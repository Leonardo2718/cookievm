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
use std::cmp;
use std::iter::Iterator;
use std::str::Chars;
use std::num;
use std::error;
use std::result;
use std::convert;

#[derive(Debug,Clone,Copy,PartialEq)]
pub struct Position<'a> {
    pub source: &'a str,
    pub position: usize,
    pub line: usize,
    pub column: usize
}

impl<'a> fmt::Display for Position<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(line {}, columnt {})", self.line, self.column)
    }
}

impl<'a> cmp::PartialOrd<Position<'a>> for Position<'a> {
    fn partial_cmp(& self, &rhs: &Position) -> Option<cmp::Ordering> {
        if self.source != rhs.source { None }
        else { self.position.partial_cmp(&rhs.position) }
    }
}

#[derive(Debug,Clone)]
struct CharPos<'a> {
    c: char,
    pos: Position<'a>
}

#[derive(Debug,Clone)]
struct CharPosIter<'a> {
    current: char,
    pos: Position<'a>,
    iter: Chars<'a>
}

impl<'a> CharPosIter<'a> {
    fn new<'b>(src: &'b str) -> CharPosIter<'b> {
        CharPosIter{current: '\0', pos: Position{source: src, position: 0, line: 1, column: 0}, iter: src.chars()}
    }
}

impl<'a> Iterator for CharPosIter<'a> {
    type Item = CharPos<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(c) => {
                self.pos.position += 1;
                match self.current {
                    '\n' => { self.pos.line += 1; self.pos.column = 1; }
                    _ => { self.pos.column += 1; }
                };
                self.current = c;
                Some(CharPos{c: self.current, pos: self.pos})
            }
            None => None
        }
    }
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
    StackPos(usize),
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

#[derive(Debug,Clone,PartialEq)]
pub struct TokenPos<'a> {
    pub token: Token,
    pub pos: Position<'a>,
}

#[derive(Debug,Clone,PartialEq)]
pub enum LexerError {
    ExpectingMoreCharacters,
    UnexpectedCharacter(char),
    ParseIntError(num::ParseIntError),
    ParseFloatError(num::ParseFloatError),
}

impl fmt::Display for LexerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug,Clone)]
pub struct Error<'a> {
    err: LexerError,
    pos: Position<'a>
}

impl<'a> error::Error for Error<'a> {
    fn description(&self) -> &str {
        use self::LexerError::*;
        match self.err {
            ExpectingMoreCharacters => "Lexer expected more characters for a complete token",
            UnexpectedCharacter(_) => "Lexer encountered an unexpected character",
            ParseIntError(_) => "Lexer failed to parse character sequence as an integer value (see cause)",
            ParseFloatError(_) => "Lexer failed to parse character sequence as a floating point value (see cause)",
        }
    }

    fn cause(&self) -> Option<&error::Error> {
        match self.err {
            LexerError::ParseIntError(ref e) => Some(e),
            LexerError::ParseFloatError(ref e) => Some(e),
            _ => None
        }
    }
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

type Result<'a> = result::Result<TokenPos<'a>,Error<'a>>;

impl convert::From<LexerError> for String {
    fn from(error: LexerError) -> Self {
        error.to_string()
    }
}

pub struct Lexer<'a> {
    iter: CharPosIter<'a>,
    token_pos: Position<'a>
}

macro_rules! eat_while {
    ($s:expr, $pred:expr, $eater:expr) => (
        loop {
            match $s.peek_char() {
                Some(c) if $pred(c) => {$s.next_char(); $eater(c)},
                _ => break,
            }
        }
    )
}

macro_rules! emit_err {
    ($this:expr,$err:expr) => {
        Err(Error{err:$err, pos: $this.token_pos})
    };
}

macro_rules! ret_err {
    ($this:expr,$err:expr) => {
        return emit_err!($this, $err)
    };
}

impl<'a> Lexer<'a> {
    pub fn new<'b>(src: &'b str) -> Lexer<'b> {
        Lexer{iter: CharPosIter::new(src), token_pos: Position{source: src, position: 1, line: 1, column: 1} }
    }

    fn next_char(&mut self) -> Option<char> {
        self.iter.next().map(|i| i.c)
    }

    fn peek_char(&mut self) -> Option<char> {
        self.iter.clone().peekable().peek().map(|i| i.c)
    }

    fn move_and_set_pos(&mut self) -> result::Result<(), Error<'a>>{
        match self.iter.next() {
            Some(c) => { self.token_pos = c.pos; Ok(())}
            None => {emit_err!(self, LexerError::ExpectingMoreCharacters)}
        }
    }

    fn emit(&self, t: Token) -> Result<'a> {
        Ok(TokenPos{token:t, pos: self.token_pos})
    }

    fn match_decimal(&mut self, init: char) -> Result<'a> {
        let mut s = String::new();
        s.push(init);
        let is_num = |c:char| c.is_digit(10);
        eat_while!(self, is_num, |c:char| s.push(c));
        match self.peek_char() {
            Some('.') => {
                self.next_char();
                s.push('.');
                eat_while!(self, is_num, |c:char| s.push(c));
                let f = s.clone().parse::<f32>().map_err(|e| Error{err: LexerError::ParseFloatError(e), pos: self.token_pos})?;
                self.emit(Token::Float(f))
            },
            _ => {
                let i = s.clone().parse::<i32>().map_err(|e| Error{err: LexerError::ParseIntError(e), pos: self.token_pos})?;
                self.emit(Token::Integer(i))
            }
        }
    }

    fn match_negative(&mut self) -> Result<'a> {
        let c = self.next_char().ok_or(Error{err: LexerError::ExpectingMoreCharacters, pos: self.token_pos})?;
        let t = self.match_decimal(c)?;
        match t.token {
            Token::Float(f) => Ok(TokenPos{token: Token::Float(-f), pos: t.pos}),
            Token::Integer(i) => Ok(TokenPos{token: Token::Integer(-i), pos: t.pos}),
            _ => panic!("`match_decimal() returned neither an Interger nor Float token (scanner position: {})!", self.token_pos)
        }
    }

    fn match_hex(&mut self) -> Result<'a> {
        let mut s = String::new();
        let is_hex = |c:char| c.is_digit(16);
        eat_while!(self, is_hex, |c:char| s.push(c));
        let addr = usize::from_str_radix(s.as_ref(), 16).map_err(|e| Error{err: LexerError::ParseIntError(e), pos: self.token_pos})?;
        self.emit(Token::Address(addr))
    }

    fn match_char(&mut self) -> Result<'a> {
        let c = match self.next_char() {
            Some('\\') => {
                match self.next_char() {
                    Some('\'') => '\'',
                    Some('\\') => '\\',
                    Some('t') => '\t',
                    Some('n') => '\n',
                    Some('r') => '\r',
                    Some(c) => c,
                    None => ret_err!(self, LexerError::ExpectingMoreCharacters)
                }
            },
            Some(c) => c,
            _ => ret_err!(self, LexerError::ExpectingMoreCharacters)
        };
        self.emit(Token::Char(c))
    }

    fn match_stack_pos(&mut self) -> Result<'a> {
        let mut s = String::new();
        eat_while!(self, |c:char| c.is_digit(10), |c:char| s.push(c));
        let pos = s.clone().parse::<usize>().map_err(|e| Error{err: LexerError::ParseIntError(e), pos: self.token_pos})?;
        self.emit(Token::StackPos(pos))
    }

    fn match_reg(&mut self) -> Result<'a> {
        let mut s = String::new();
        match self.peek_char() {
            Some(c) if c.is_numeric() => {
                let is_gpr = |c:char| c.is_numeric();
                eat_while!(self, is_gpr, |c:char| s.push(c));
                let reg_num = u8::from_str_radix(s.as_ref(), 10).map_err(|e| Error{err: LexerError::ParseIntError(e), pos: self.token_pos})?;
                self.emit(Token::R(reg_num))
            },
            Some(c) if c.is_alphabetic() => {
                let is_reg = |c:char| c.is_alphabetic();
                eat_while!(self, is_reg, |c:char| s.push(c));
                return match s.as_ref() {
                    "sp" => self.emit(Token::SP),
                    "fp" => self.emit(Token::FP),
                    "pc" => self.emit(Token::PC),
                    _ => emit_err!(self, LexerError::ExpectingMoreCharacters)
                };
            }
            _ => ret_err!(self, LexerError::ExpectingMoreCharacters)
        }
    }

    fn match_ident(&mut self, init: char) -> Result<'a> {
        let mut s = String::new();
        s.push(init);
        let is_ident = |c:char| c.is_alphanumeric() || c == '_';
        eat_while!(self, is_ident, |c:char| s.push(c));
        return match s.to_lowercase().as_ref() {
            "true" => self.emit(Token::Bool(true)),
            "false" => self.emit(Token::Bool(false)),
            "void" => self.emit(Token::Void),
            _ => match self.peek_char() {
                Some(':') => { self.next_char(); self.emit(Token::Label(s)) },
                _ => self.emit(Token::Ident(s))
            }
        };
    }

    fn match_num(&mut self) -> Result<'a> {
        // If the current character is 0 and the next one is "x",
        // then the number must be in hex, otherwise it is in decimal
        match self.peek_char() {
            Some('0') => {
                self.move_and_set_pos()?;
                match self.peek_char() {
                    Some('x') => {self.next_char(); self.match_hex()},
                    _ => self.match_decimal('0')
                }
            },
            Some(c) => { self.move_and_set_pos()?; self.match_decimal(c) },
            None => panic!("Called `match_num()` but character stream ended; last scanner position is {}", self.token_pos)
        }
    }
}

macro_rules! lexer_try {
    ($e:expr) => {
        match $e {
            Ok(r) => r,
            Err(e) => return Some(Err(e))
        }
    };
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<'a>;

    fn next(&mut self) -> Option<Result<'a>> {
        loop {
            match self.peek_char() {
                Some('(') => { lexer_try!(self.move_and_set_pos()); return Some(self.emit(Token::LParen)); }
                Some(')') => { lexer_try!(self.move_and_set_pos()); return Some(self.emit(Token::RParen)); }
                Some('.') => { lexer_try!(self.move_and_set_pos()); return Some(self.emit(Token::Dot)); }
                Some(';') => { eat_while!(self, |c| c != '\n', |_| ()); self.next_char(); continue; }
                Some('-') => { lexer_try!(self.move_and_set_pos()); let r = self.match_negative(); return Some(r); }
                Some(c) if c.is_whitespace() => { lexer_try!(self.move_and_set_pos()); continue; }
                Some('\'') => {
                    // when the current character is a ' , return the next character (or two if \ )
                    // and check there is a closing '
                    lexer_try!(self.move_and_set_pos());
                    let t = Some(self.match_char());
                    match self.next_char() {
                        Some('\'') => return t,
                        Some(c) => return Some(emit_err!(self, LexerError::UnexpectedCharacter(c))),
                        None => return Some(emit_err!(self, LexerError::ExpectingMoreCharacters))
                    };
                }
                Some('@') => {
                    // an @ indicates the start of a stack position 
                    lexer_try!(self.move_and_set_pos());
                    return Some(self.match_stack_pos());
                }
                Some('$') => {
                    // a $ indicates the start of a register name, so the next characters must either
                    // be numeric (for a GPR) or the name of a special register
                    lexer_try!(self.move_and_set_pos());
                    return Some(self.match_reg());
                }
                Some(c) if c.is_alphabetic() || c == '_' => {
                    // when a character is alphabetic or an _ , it indicates the start of an identifer
                    // which can either be one of the "special" identifiers (keywords) or a generic
                    // name (e.g. a label reference)
                    lexer_try!(self.move_and_set_pos());
                    return Some(self.match_ident(c));
                }
                Some(c) if c.is_digit(10) => {
                    // A numeric character indicates the start of a number
                    return Some(self.match_num());
                }
                Some(c) => return Some(emit_err!(self, LexerError::UnexpectedCharacter(c))),
                None => { return None; }
            }
        }
    }
}

#[cfg(test)]
mod test{
    use super::*;
    use self::Token::*;

    macro_rules! assert_next_is {
        ($lexer:expr, $token:expr, $pos:expr, $line:expr, $col:expr) => {
            let t = $lexer.next();
            assert!(t.is_some(), "t = {:?}", t);
            let t = t.unwrap();
            assert!(t.is_ok(), "t = {:?}", t);
            let t = t.unwrap();
            assert_eq!(t.token, $token, "Wrong token");
            assert_eq!(t.pos.position, $pos, "Wrong file position");
            assert_eq!(t.pos.line, $line, "Wrong line number");
            assert_eq!(t.pos.column, $col, "Wrong column number");
        };
    }

    #[test]
    fn lexer_test_1() {
        let mut lexer = Lexer::new("1234");
        assert_next_is!(lexer, Integer(1234), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_2() {
        let mut lexer = Lexer::new("I32");
        assert_next_is!(lexer, Ident("I32".to_string()), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_3() {
        let mut lexer = Lexer::new("2.71828");
        assert_next_is!(lexer, Float(2.71828), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_4() {
        let mut lexer = Lexer::new("0xabcd1234");
        assert_next_is!(lexer, Address(0xabcd1234), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_5() {
        let mut lexer = Lexer::new("(");
        assert_next_is!(lexer, LParen, 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_6() {
        let mut lexer = Lexer::new(")");
        assert_next_is!(lexer, RParen, 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_7() {
        let mut lexer = Lexer::new(".");
        assert_next_is!(lexer, Dot, 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_8() {
        let mut lexer = Lexer::new("'e'");
        assert_next_is!(lexer, Char('e'), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_9() {
        let mut lexer = Lexer::new(r"'\n'");
        assert_next_is!(lexer, Char('\n'), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_10() {
        let mut lexer = Lexer::new(r"'\f'");
        assert_next_is!(lexer, Char('f'), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_11() {
        let mut lexer = Lexer::new(r"'\\'");
        assert_next_is!(lexer, Char('\\'), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_12() {
        let mut lexer = Lexer::new("foo:");
        assert_next_is!(lexer, Label("foo".to_string()), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_13() {
        let mut lexer = Lexer::new("true");
        assert_next_is!(lexer, Bool(true), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_14() {
        let mut lexer = Lexer::new("false");
        assert_next_is!(lexer, Bool(false), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_15() {
        let mut lexer = Lexer::new(" F32 ( 3.14159 ) ");
        assert_next_is!(lexer, Ident("F32".to_string()), 2, 1, 2);
        assert_next_is!(lexer, LParen, 6, 1, 6);
        assert_next_is!(lexer, Float(3.14159), 8, 1, 8);
        assert_next_is!(lexer, RParen, 16, 1, 16);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_16() {
        let mut lexer = Lexer::new("0xabcdefg");
        assert_next_is!(lexer, Address(0xabcdef), 1, 1, 1);
        assert_next_is!(lexer, Ident("g".to_string()), 9, 1, 9);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_17() {
        let mut lexer = Lexer::new("true:");
        assert_next_is!(lexer, Bool(true), 1, 1, 1);
        assert!(lexer.next().unwrap().is_err());
    }

    #[test]
    fn lexer_test_18() {
        let mut lexer = Lexer::new("foo0x123");
        assert_next_is!(lexer, Ident("foo0x123".to_string()), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_19() {
        let mut lexer = Lexer::new("; some text");
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_20() {
        let mut lexer = Lexer::new(r"'\n' ; 0x123");
        assert_next_is!(lexer, Char('\n'), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_21() {
        let mut lexer = Lexer::new("Void");
        assert_next_is!(lexer, Void, 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_22() {
        let mut lexer = Lexer::new("I32(3)");
        assert_next_is!(lexer, Ident("I32".to_string()), 1, 1, 1);
        assert_next_is!(lexer, LParen, 4, 1, 4);
        assert_next_is!(lexer, Integer(3), 5, 1, 5);
        assert_next_is!(lexer, RParen, 6, 1, 6);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_23() {
        let mut lexer = Lexer::new("$sp");
        assert_next_is!(lexer, SP, 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_24() {
        let mut lexer = Lexer::new("$fp");
        assert_next_is!(lexer, FP, 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_25() {
        let mut lexer = Lexer::new("$pc");
        assert_next_is!(lexer, PC, 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_26() {
        let mut lexer = Lexer::new("$0");
        assert_next_is!(lexer, R(0), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_27() {
        let mut lexer = Lexer::new(" foo L1: bar");
        assert_next_is!(lexer, Ident("foo".to_string()), 2, 1, 2);
        assert_next_is!(lexer, Label("L1".to_string()), 6, 1, 6);
        assert_next_is!(lexer, Ident("bar".to_string()), 10, 1, 10);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_28() {
        let mut lexer = Lexer::new("L1:L2:");
        assert_next_is!(lexer, Label("L1".to_string()), 1, 1, 1);
        assert_next_is!(lexer, Label("L2".to_string()), 4, 1, 4);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_29() {
        let mut lexer = Lexer::new("-234");
        assert_next_is!(lexer, Integer(-234), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_30() {
        let mut lexer = Lexer::new("-5.43");
        assert_next_is!(lexer, Float(-5.43), 1, 1, 1);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_31() {
        let mut lexer = Lexer::new("F32 ( -6.78 )");
        assert_eq!(lexer.next().unwrap().unwrap().token, Token::Ident("F32".to_string()));
        assert_eq!(lexer.next().unwrap().unwrap().token, Token::LParen);
        assert_eq!(lexer.next().unwrap().unwrap().token, Token::Float(-6.78));
        assert_eq!(lexer.next().unwrap().unwrap().token, Token::RParen);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_32() {
        let mut lexer = Lexer::new("\n  -foo");
        let e = lexer.next().unwrap();
        assert!(e.clone().is_err());
        assert_eq!(e.clone().unwrap_err().pos.line, 2);
        assert_eq!(e.clone().unwrap_err().pos.column, 3);
    }

    #[test]
    fn lexer_test_33() {
        let mut lexer = Lexer::new("0");
        assert_next_is!(lexer, Integer(0), 1, 1, 1);
    }
}
