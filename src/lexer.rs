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

use cookie_base;
use std::fmt;
use std::iter::Iterator;
use std::str::Chars;

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
        for _ in 0..$count { $iter.next(); }
    )
}

macro_rules! peek {
    ($iter:expr) => (
        $iter.clone().peekable().peek()
    )
}

type Result = cookie_base::Result<Token>;

pub struct Lexer<'a> {
    iter: Chars<'a>,
}

impl<'a> Lexer<'a> {
    pub fn new<'b>(iter: Chars<'b>) -> Lexer<'b> {
        Lexer{iter: iter}
    }

    fn match_decimal(&mut self) -> Result {
        let mut s = String::new();
        let is_num = |c:&char| c.is_digit(10);
        eat_while!(self.iter.by_ref(), is_num, |c:&char| s.push(*c));
        match self.iter.clone().peekable().peek() {
            Some('.') => {
                skip_n!(self.iter,1);
                s.push('.');
                eat_while!(self.iter.by_ref(), is_num, |c:&char| s.push(*c));
                let num = s.clone().parse::<f32>();
                return num.map(|f:f32| Token::Float(f)).map_err(|e| e.to_string());
            },
            _ => {
                let num = s.clone().parse::<i32>();
                return num.map(|i:i32| Token::Integer(i)).map_err(|e| e.to_string());
            }
        }
    }

    fn match_negative(&mut self) -> Result {
        let t = self.match_decimal()?;
        match t {
            Token::Float(f) => Ok(Token::Float(-f)),
            Token::Integer(i) => Ok(Token::Integer(-i)),
            _ => Err(format!("Cannot take negative of non-integer/non-float token: {}", t))
        }
    }

    fn match_hex(&mut self) -> Result {
        let mut s = String::new();
        let is_hex = |c:&char| c.is_digit(16);
        eat_while!(self.iter.by_ref(), is_hex, |c:&char| s.push(*c));
        let addr = usize::from_str_radix(s.as_ref(), 16);
        return addr.map(|a:usize| Token::Address(a)).map_err(|e| e.to_string());
    }

    fn match_char(&mut self) -> Result {
        let c = match self.iter.next() {
            Some('\\') => {
                match self.iter.next() {
                    Some('\'') => '\'',
                    Some('\\') => '\\',
                    Some('t') => '\t',
                    Some('n') => '\n',
                    Some('r') => '\r',
                    Some(c) => c,
                    None => return Err("Unexpected end of character stream".to_string())
                }
            },
            Some(c) => c,
            _ => return Err("Unexpected end of character stream".to_string())
        };
        Ok(Token::Char(c))
    }

    fn match_reg(&mut self) -> Result {
        let mut s = String::new();
        match self.iter.clone().peekable().peek() {
            Some(c) if c.is_numeric() => {
                let is_gpr = |c:&char| c.is_numeric();
                eat_while!(self.iter, is_gpr, |c:&char| s.push(*c));
                let reg_num = u8::from_str_radix(s.as_ref(), 10);
                reg_num.map(|i:u8| Token::R(i)).or(Err("Failed to parse GPR number".to_string()))
            },
            Some(c) if c.is_alphabetic() => {
                let is_reg = |c:&char| c.is_alphabetic();
                eat_while!(self.iter, is_reg, |c:&char| s.push(*c));
                return match s.as_ref() {
                    "sp" => Ok(Token::SP),
                    "fp" => Ok(Token::FP),
                    "pc" => Ok(Token::PC),
                    _ => Err("Unexpected end of character stream".to_string())
                };
            }
            _ => return Err("Unexpected end of character stream".to_string())
        }
    }

    fn match_ident(&mut self) -> Result {
        let mut s = String::new();
        let is_ident = |c:&char| c.is_alphanumeric() || c == &'_';
        eat_while!(self.iter.by_ref(), is_ident, |c:&char| s.push(*c));
        return match s.to_lowercase().as_ref() {
            "true" => Ok(Token::Bool(true)),
            "false" => Ok(Token::Bool(false)),
            "void" => Ok(Token::Void),
            _ => match peek!(self.iter) {
                Some(&':') => { skip_n!(self.iter, 1); Ok(Token::Label(s)) },
                _ => Ok(Token::Ident(s))
            }
        };
    }

    fn match_num(&mut self) -> Result {
        // If the current character is 0 and the next one is "x",
        // then the number must be in hex, otherwise it is in decimal
        let mut iter_clone = self.iter.clone();
        return match (iter_clone.next(), iter_clone.next()) {
            (Some('0'), Some('x')) => {
                skip_n!(self.iter,2);
                self.match_hex()
            },
            _ => self.match_decimal()
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result;

    fn next(&mut self) -> Option<Result> {
        macro_rules! emit_token {
            ($token:expr) => ( return Some(Ok($token)) )
        }

        macro_rules! emit_err {
            ($($err:expr),+) => ( return Some(Err(format!($($err),+))) )
        }

        loop {
            match peek!(self.iter) {
                Some(&'(') => { skip_n!(self.iter,1); emit_token!(Token::LParen); }
                Some(&')') => { skip_n!(self.iter,1); emit_token!(Token::RParen); }
                Some(&'.') => { skip_n!(self.iter,1); emit_token!(Token::Dot); }
                Some(&';') => { eat_while!(self.iter.by_ref(), |c| c != &'\n', |_| ()); skip_n!(self.iter,1); continue; }
                Some(&'-') => { skip_n!(self.iter,1); return Some(self.match_negative()); }
                Some(c) if c.is_whitespace() => { skip_n!(self.iter,1); continue; }
                Some(&'\'') => {
                    // when the current character is a ' , return the next character (or two if \ )
                    // and check there is a closing '
                    skip_n!(self.iter,1);
                    let t = Some(self.match_char());
                    match self.iter.next() {
                        Some('\'') => return t,
                        _ => emit_err!("Unexpected end of character stream")
                    };
                }
                Some(&'$') => {
                    // a $ indicates the start of a register name, so the next characters must either
                    // be numeric (for a GPR) or the name of a special register
                    skip_n!(self.iter, 1);
                    return Some(self.match_reg());
                }
                Some(c) if c.is_alphabetic() || c == &'_' => {
                    // when a character is alphabetic or an _ , it indicates the start of an identifer
                    // which can either be one of the "special" identifiers (keywords) or a generic
                    // name (e.g. a label reference)
                    return Some(self.match_ident());
                }
                Some(c) if c.is_digit(10) => {
                    // A numeric character indicates the start of a number
                    return Some(self.match_num());
                }
                Some(c) => emit_err!("Unexpected character {}", c),
                None => { return None; }
            }
        }
    }
}

#[cfg(test)]
mod test{
    use super::*;

    #[test]
    fn lexer_test_1() {
        let mut lexer = Lexer::new("1234".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Integer(1234));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_2() {
        let mut lexer = Lexer::new("I32".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Ident("I32".to_string()));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_3() {
        let mut lexer = Lexer::new("2.71828".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Float(2.71828));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_4() {
        let mut lexer = Lexer::new("0xabcd1234".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Address(0xabcd1234));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_5() {
        let mut lexer = Lexer::new("(".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::LParen);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_6() {
        let mut lexer = Lexer::new(")".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::RParen);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_7() {
        let mut lexer = Lexer::new(".".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Dot);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_8() {
        let mut lexer = Lexer::new("'e'".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Char('e'));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_9() {
        let mut lexer = Lexer::new(r"'\n'".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Char('\n'));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_10() {
        let mut lexer = Lexer::new(r"'\f'".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Char('f'));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_11() {
        let mut lexer = Lexer::new(r"'\\'".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Char('\\'));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_12() {
        let mut lexer = Lexer::new("foo:".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Label("foo".to_string()));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_13() {
        let mut lexer = Lexer::new("true".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Bool(true));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_14() {
        let mut lexer = Lexer::new("false".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Bool(false));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_15() {
        let mut lexer = Lexer::new(" F32 ( 3.14159 ) ".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Ident("F32".to_string()));
        assert_eq!(lexer.next().unwrap().unwrap(), Token::LParen);
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Float(3.14159));
        assert_eq!(lexer.next().unwrap().unwrap(), Token::RParen);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_16() {
        let mut lexer = Lexer::new("0xabcdefg".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Address(0xabcdef));
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Ident("g".to_string()));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_17() {
        let mut lexer = Lexer::new("true:".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Bool(true));
        assert!(lexer.next().unwrap().is_err());
    }

    #[test]
    fn lexer_test_18() {
        let mut lexer = Lexer::new("foo0x123".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Ident("foo0x123".to_string()));
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
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Char('\n'));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_21() {
        let mut lexer = Lexer::new("Void".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Void);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_22() {
        let mut lexer = Lexer::new("I32(3)".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Ident("I32".to_string()));
        assert_eq!(lexer.next().unwrap().unwrap(), Token::LParen);
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Integer(3));
        assert_eq!(lexer.next().unwrap().unwrap(), Token::RParen);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_23() {
        let mut lexer = Lexer::new("$sp".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::SP);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_24() {
        let mut lexer = Lexer::new("$fp".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::FP);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_25() {
        let mut lexer = Lexer::new("$pc".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::PC);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_26() {
        let mut lexer = Lexer::new("$0".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::R(0));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_27() {
        let mut lexer = Lexer::new(" foo L1: bar".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Ident("foo".to_string()));
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Label("L1".to_string()));
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Ident("bar".to_string()));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_28() {
        let mut lexer = Lexer::new("L1:L2:".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Label("L1".to_string()));
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Label("L2".to_string()));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_29() {
        let mut lexer = Lexer::new("-234".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Integer(-234));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_30() {
        let mut lexer = Lexer::new("-5.43".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Float(-5.43));
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_31() {
        let mut lexer = Lexer::new("F32 ( -6.78 )".chars());
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Ident("F32".to_string()));
        assert_eq!(lexer.next().unwrap().unwrap(), Token::LParen);
        assert_eq!(lexer.next().unwrap().unwrap(), Token::Float(-6.78));
        assert_eq!(lexer.next().unwrap().unwrap(), Token::RParen);
        assert!(lexer.next().is_none());
    }

    #[test]
    fn lexer_test_32() {
        let mut lexer = Lexer::new("-foo".chars());
        assert!(lexer.next().unwrap().is_err());
    }
}
