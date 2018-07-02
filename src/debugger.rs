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
use interpreter::Interpreter;
use interpreter::Status;
use interpreter::InterpreterError;

use std::fmt;
use std::error;
use std::convert;
use std::result;
use std::cmp;
use rustyline;

#[derive(Debug,Clone,PartialEq)]
enum DebugState {
    Running, // program is running (in debugger)
    Paused,  // program execution is paused
}

#[derive(Debug)]
pub enum DebugError {
    ProgramTerminatedByUser,
    UnhandledInterpreterError(InterpreterError),
    ReadLineError(rustyline::error::ReadlineError)
}

impl fmt::Display for DebugError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl error::Error for DebugError {
    fn description(&self) -> &str {
        use self::DebugError::*;
        match self {
            &ProgramTerminatedByUser => "Premature program termination caused by user",
            &UnhandledInterpreterError(_) => "An interpreter error occurred that is not handled by the debugger",
            &ReadLineError(_) => "readline/rustyline generated an unexpected error (see cause)"
        }
    }

    fn cause(&self) -> Option<&error::Error> {
        use self::DebugError::*;
        match self {
            &UnhandledInterpreterError(ref e) => Some(e),
            &ReadLineError(ref e) => Some(e),
            _ => None
        }
    }
}

impl convert::From<InterpreterError> for DebugError {
    fn from(error: InterpreterError) -> Self {
        DebugError::UnhandledInterpreterError(error)
    }
}

pub type Result<T> = result::Result<T, DebugError>;

/*
The `Debugger` struct encapsulates the environment for debugging cookie code
*/
pub struct Debugger {
    interp: Interpreter,
    status: Status,
    debug_state: DebugState,
}

impl Debugger {
    pub fn new(instructions: cookie::InstructionList) -> Debugger {
        Debugger { interp: Interpreter::new(instructions)
                 , status: Status::Ok
                 , debug_state: DebugState::Paused
                 }
    }

    fn print_stack(&self) {
        macro_rules! stack_point {
            ($pos:expr) => (
                if $pos == self.interp.stack.len() && $pos == self.interp.fp { "<= $sp, $fp" }
                else if $pos == self.interp.fp { "<= $fp" }
                else if $pos == self.interp.stack.len() { "<= $sp" }
                else { "" }
            )
        }

        for (pos, val) in self.interp.stack.iter().enumerate().rev() {
            let pos = pos + 1;
            let point = stack_point!(pos);
            println!("0x{:08x} {:12}{}", pos, val.to_string(), point);
        }
        println!("----------");
        println!("0x{:08x} {:12}{}", 0, cookie::Value::Void.to_string(), stack_point!(0));
    }

    fn list_instructions(&self, start: usize, count: usize) {
        let start = cmp::max(0, start);
        let end = start + count;
        let end = cmp::min(self.interp.instructions.len(), end);
        for i in start..end {
            let pointer = if i == self.interp.pc {"$pc => "} else { "       " };
            println!("{}0x{:08x} {:?}", pointer, i, self.interp.instructions[i]);
        }
    }

    pub fn debug(&mut self) -> Result<()> {
        use rustyline::error::ReadlineError;
        use rustyline::Editor;

        let mut prompt = Editor::<()>::new();  // command-line style prompt

        macro_rules! usub {
            ($l:expr, $r:expr) => { $l - cmp::min($l, $r) };
        }

        macro_rules! debug_quit {
            () => ({
                if self.status == Status::Finish { break; }
                else {
                    let readline = prompt.readline("Program thread is still running, are you sure you want to quit (y/n): ");
                    match readline {
                        Ok(ref r) if r == "y" => return Err(DebugError::ProgramTerminatedByUser),
                        _ => continue,
                    }
                }
            })
        }

        loop {
            if self.debug_state == DebugState::Running {
                if self.interp.pc >= self.interp.instructions.len() { self.debug_state = DebugState::Paused; continue; }
                match self.interp.exec_next() {
                    Err(msg) => { println!("{}", msg); self.debug_state = DebugState::Paused; }
                    _ => continue,
                };
            } else {
                let readline = prompt.readline(">> ");
                match readline {
                    Ok(cmd) => { prompt.add_history_entry(cmd.as_ref()); match cmd.as_ref() {
                        "l" | "list" => self.list_instructions(usub!(self.interp.pc, 2), 5),
                        "bt" | "stack" | "backtrace" => self.print_stack(),
                        "c" | "continue" | "r" | "run" => self.debug_state = DebugState::Running,
                        "s" | "step" => { self.interp.exec_next()?; }
                        "q" | "quit" => debug_quit!(),
                        "" => continue,
                        _ => println!("Error: unknown command {:?}", cmd),
                    };},
                    Err(ReadlineError::Eof) => continue,
                    Err(ReadlineError::Interrupted) => continue,
                    Err(_) => break,
                };
            }
        }

        return Ok(());
    }
}
