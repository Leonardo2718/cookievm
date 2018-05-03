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

#[derive(Debug,Clone,PartialEq)]
pub enum Type {
    I32,
    F32,
    Char,
    Bool,
    CodeAddr,
    StackAddr,
}

#[derive(Debug,Clone,PartialEq)]
pub enum Value {
    I32(i32),
    F32(f32),
    Char(char),
    Bool(bool),
    CodeAddr(u32),
    StackAddr(u32),
}

impl Value {
    pub fn get_type(&self) -> Type {
        match self {
            &Value::I32(_) => Type::I32,
            &Value::F32(_) => Type::F32,
            &Value::Char(_) => Type::Char,
            &Value::Bool(_) => Type::Bool,
            &Value::CodeAddr(_) => Type::CodeAddr,
            &Value::StackAddr(_) => Type::StackAddr,
        }
    }

    pub fn is_type(&self, t: Type) -> bool { t == self.get_type() }
}

#[derive(Debug)]
pub enum Register {
    StackPointer,
    FramPointer,
    ProgramCounter,
    IReg(u8),
    FReg(u8),
}

#[derive(Debug)]
pub enum Instruction {
    PUSHR(Register),
    PUSHC(Value),
    POPR(Register),
    POP,

    ADDS(Type),
    SUBS(Type),
    MULS(Type),
    DIVS(Type),
    MODS(Type),

    ANDS(Type),
    ORS(Type),
    XORS(Type),
    NOTS(Type),

    EQ(Type),
    LT(Type),
    LE(Type),
    GT(Type),
    GE(Type),

    JUMP(String),
    JUMPS,
    JUMPO(Value),
    BRANCHEQS(Value, String),
    BRANCHNES(Value, String),

    PRINTS(Type),
    READS(Type),

    HALT,
}
