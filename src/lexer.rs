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

use interpreter::*;
use std::fmt;
use std::iter::Iterator;
use std::str::Chars;

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
        for _ in 0..$count { $iter.next(); }
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

#[cfg(test)]
mod test{
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
}
