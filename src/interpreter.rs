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

use cookie_base as cookie;

pub type InstructionList = Vec<cookie::Instruction>;
pub type Stack = Vec<cookie::Value>;

fn print_stack(stack: &Stack) {
    print!("[");
    for elem in stack {
        print!("{:?}, ", elem);
    }
    println!("]");
}

pub fn exec(instructions: &InstructionList) -> Result<Option<cookie::Value>,String> {
    use cookie_base::Instruction::*;
    let mut stack: Stack = Vec::new();
    for inst in instructions {
        match inst {
            PUSHC(v) => stack.push(v.clone()),
            POP => { stack.pop().ok_or("Connot pop value from stack: stack is empty.")?; }
            PRINTS(t) => {
                let v = stack.pop().ok_or("Cannot print stack value: stack is empty.")?;
                if !v.is_type(t.clone()) { return Err(format!("Attempting to print stack value of type {:?} as type {:?}", v.get_type(), t)); }
                println!("{:?}", v);
            },
            _ => return Err("Unimplemented instruction".to_string())
        };
        // print_stack(&stack);
    }
    return Ok(None);
}
