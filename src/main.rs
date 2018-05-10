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

#![feature(transpose_result)]

use std::env::args;
use std::io;
use std::io::prelude::*;
use std::fs::File;
use std::io::BufReader;
use std::collections::HashMap;

mod cookie_base;
mod interpreter;
mod parser;

fn main() {
    use cookie_base::*;
    use interpreter::*;
    use parser::*;

    let fpath = args().nth(1).ok_or("Usage: cookie PATH").unwrap();
    let f = File::open(fpath).unwrap();
    let mut reader = BufReader::new(f);
    let mut source = String::new();
    reader.read_to_string(&mut source);

    let (instructions, labels) = parse(Lexer::new(source.chars())).unwrap();

    let mut thread = Thread::new(&instructions, labels);
    match thread.exec() {
        Ok(Some(v)) => println!("\n-----\n{}", v),
        Ok(None) => println!("\n-----"),
        Err(msg) => println!("{}", msg),
    }
}
