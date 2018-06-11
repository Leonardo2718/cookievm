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

use std::io::prelude::Read;
use std::fs::File;
use std::io::BufReader;

mod cookie_base;
mod interpreter;
mod lexer;
mod parser;

extern crate rustyline;
extern crate argparse;

struct Options {
    source_path: String,
    debug: bool
}

fn main() {
    use interpreter::*;
    use lexer::*;
    use parser::*;

    let mut options = Options{source_path: "".to_string(), debug: false};
    {
        use argparse as ap;
        let mut parser = ap::ArgumentParser::new();
        parser.set_description("The cookie VM");
        parser.refer(&mut options.debug)
            .add_option(&["-d", "--debug"], ap::StoreTrue, "run cookie code in debugger");
        parser.refer(&mut options.source_path)
            .add_argument("source_path", ap::Store, "source file to be executed").required();
        parser.parse_args_or_exit();
    }

    let mut source = String::new();
    {
        let f = File::open(options.source_path).unwrap();
        let mut reader = BufReader::new(f);
        reader.read_to_string(&mut source).unwrap(); // expect read to succeed
    }

    let (instructions, labels) = parse(Lexer::new(source.chars())).unwrap();

    let mut thread = Thread::new(&instructions, labels);
    if options.debug { match thread.debug() {
        Ok(()) => {},
        Err(msg) => println!("{}", msg),
    }}
    else { match thread.exec() {
        Ok(Some(v)) => println!("\n-----\n{}", v),
        Ok(None) => println!("\n-----"),
        Err(msg) => println!("{}", msg),
    }}
}
