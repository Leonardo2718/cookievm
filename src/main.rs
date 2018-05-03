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
    let mut instructions: InstructionList = vec![
        PUSHC(Value::I32(1)),
        PRINTS(Type::I32),
        PUSHC(Value::I32(2)),
        PRINTS(Type::I32),
        PUSHC(Value::I32(3)),
        PRINTS(Type::I32),
    ];
    match exec(&instructions) {
        Ok(_) => {},
        Err(msg) => println!("{}", msg)
    }
}
