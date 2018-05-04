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

// use std::fmt;
// use std::result;

mod cookie_base;
mod interpreter;

fn main() {
    use cookie_base::*;
    use cookie_base::Instruction::*;
    use interpreter::*;
    let instructions: InstructionList = vec![
        PUSHC(Value::I32(1)),
        PUSHC(Value::I32(2)),
        STACK_BINARY(BOp::ADD),
        STACK_UNARY(UOp::NEG),
        PRINTS,
        PUSHC(Value::Char('\n')),
        PRINTS,
        PUSHC(Value::Char('a')),
        PRINTS,
        PUSHC(Value::Char('b')),
        PRINTS,
        PUSHC(Value::Char('c')),
        PRINTS,
        PUSHC(Value::Char('\n')),
        PRINTS,
        PUSHC(Value::IPtr(0x15a)),
        PRINTS,
        PUSHC(Value::Char('\n')),
        PRINTS,
        PUSHC(Value::SPtr(0xa5f)),
        PRINTS,
        PUSHC(Value::Char('\n')),
        PRINTS,
    ];
    let mut thread = Thread::new(&instructions);
    match thread.exec() {
        Ok(_) => {},
        Err(msg) => println!("{}", msg)
    }
}
