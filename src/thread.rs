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
use interpreter::*;
use std::collections::HashMap;

/*
The `Thread` struct handles execution of Cookie code.
*/
pub struct Thread {
    interp: Interpreter,
    status: Status,
}

impl Thread {
    pub fn new(instructions: cookie::InstructionList) -> Thread {
        Thread  { interp: Interpreter::new(instructions)
                , status: Status::Ok
                }
    }

    pub fn exec(&mut self) -> Result<Option<cookie::Value>> {
        loop {
            self.status = self.interp.exec_next()?; 
            if self.status == Status::Finish { break; }
        }
        return Ok(self.interp.stack.pop());
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::cookie::*;
    use super::cookie::Instruction::*;
    use super::cookie::Target::*;

    #[test]
    fn pushc_test_1() {
        let insts = vec![
            PUSHC(Value::I32(3)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(3));
    }

    #[test]
    fn pushc_test_2() {
        let insts = vec![
            PUSHC(Value::F32(3.14159)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::F32(3.14159));
    }

    #[test]
    fn pushc_test_3() {
        let insts = vec![
            PUSHC(Value::Bool(true)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::Bool(true));
    }

    #[test]
    fn pushc_test_4() {
        let insts = vec![
            PUSHC(Value::Char('w')),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::Char('w'));
    }

    #[test]
    fn pushc_test_5() {
        let insts = vec![
            PUSHC(Value::IPtr(0x5)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::IPtr(0x5));
    }

    #[test]
    fn pushc_test_6() {
        let insts = vec![
            PUSHC(Value::SPtr(0x5)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::SPtr(0x5));
    }

    #[test]
    fn pushc_test_7() {
        let insts = vec![
            PUSHC(Value::Void),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::Void);
    }

    #[test]
    fn pop_test_1() {
        let insts = vec![
            PUSHC(Value::I32(2)),
            POP,
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().unwrap().is_none());
    }

    #[test]
    fn pop_test_2() {
        let insts = vec![
            PUSHC(Value::F32(2.71828)),
            POP,
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().unwrap().is_none());
    }

    #[test]
    fn pop_test_3() {
        let insts = vec![
            PUSHC(Value::Bool(true)),
            POP,
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().unwrap().is_none());
    }

    #[test]
    fn pop_test_4() {
        let insts = vec![
            PUSHC(Value::Void),
            POP,
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().unwrap().is_none());
    }

    #[test]
    fn binop_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::I32(2)),
            BOp(BinaryOp::ADD, Destination::Stack(0), Source::Stack(1), Source::Stack(0)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(3));
    }

    #[test]
    fn binop_test_2() {
        let insts = vec![
            PUSHC(Value::IPtr(0x7ab)),
            PUSHC(Value::I32(4)),
            BOp(BinaryOp::SUB, Destination::Stack(0), Source::Stack(1), Source::Stack(0)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::IPtr(0x7a7));
    }

    #[test]
    fn binop_test_3() {
        let insts = vec![
            PUSHC(Value::F32(4.0)),
            PUSHC(Value::I32(4)),
            BOp(BinaryOp::ADD, Destination::Stack(0), Source::Stack(1), Source::Stack(0)),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn binop_test_4() {
        let insts = vec![
            PUSHC(Value::Void),
            PUSHC(Value::I32(4)),
            BOp(BinaryOp::MUL, Destination::Stack(0), Source::Stack(1), Source::Stack(0)),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn uniop_test_1() {
        let insts = vec![
            PUSHC(Value::I32(3)),
            UOp(UnaryOp::NEG, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-3));
    }

    #[test]
    fn uniop_test_2() {
        let insts = vec![
            PUSHC(Value::F32(2.71828)),
            UOp(UnaryOp::NEG, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::F32(-2.71828));
    }

    #[test]
    fn uniop_test_3() {
        let insts = vec![
            PUSHC(Value::Bool(false)),
            UOp(UnaryOp::NOT, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::Bool(true));
    }

    #[test]
    fn uniop_test_4() {
        let insts = vec![
            PUSHC(Value::I32(0)),
            UOp(UnaryOp::NOT, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn uniop_test_5() {
        let insts = vec![
            PUSHC(Value::Void),
            UOp(UnaryOp::NOT, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn uniop_test_6() {
        let insts = vec![
            PUSHC(Value::F32(3.14)),
            UOp(UnaryOp::CVT(Type::I32), Destination::Stack(0), Source::Stack(0)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(3));
    }

    #[test]
    fn pushr_test_1() {
        let insts = vec![
            PUSHR(RegisterName::StackPointer),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::SPtr(0));
    }

    #[test]
    fn pushr_test_2() {
        let insts = vec![
            PUSHC(Value::I32(3)),
            PUSHC(Value::F32(3.14159)),
            PUSHC(Value::Char('c')),
            PUSHR(RegisterName::StackPointer),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::SPtr(3));
    }

    #[test]
    fn pushr_test_3() {
        let insts = vec![
            PUSHC(Value::I32(3)),
            PUSHC(Value::F32(3.14159)),
            PUSHC(Value::Char('c')),
            POP,
            PUSHR(RegisterName::StackPointer),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::SPtr(2));
    }

    #[test]
    fn pushr_test_4() {
        let insts = vec![
            PUSHR(RegisterName::ProgramCounter),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::IPtr(0));
    }

    #[test]
    fn pushr_test_5() {
        let insts = vec![
            PUSHC(Value::I32(3)),
            PUSHC(Value::F32(3.14159)),
            PUSHC(Value::Char('c')),
            PUSHR(RegisterName::ProgramCounter),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::IPtr(3));
    }

    #[test]
    fn pushr_test_6() {
        let insts = vec![
            PUSHC(Value::I32(3)),
            PUSHC(Value::F32(3.14159)),
            PUSHC(Value::Char('c')),
            POP,
            PUSHR(RegisterName::ProgramCounter),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::IPtr(4));
    }

    #[test]
    fn popr_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::I32(2)),
            PUSHC(Value::I32(3)),
            PUSHC(Value::I32(4)),
            PUSHC(Value::SPtr(2)),
            POPR(RegisterName::StackPointer),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(2));
    }

    #[test]
    fn popr_test_2() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            POPR(RegisterName::StackPointer),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn popr_test_3() {
        let insts = vec![
            PUSHC(Value::IPtr(0x0)),
            POPR(RegisterName::StackPointer),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn popr_test_4() {
        let insts = vec![
            PUSHC(Value::SPtr(0x2)),
            POPR(RegisterName::ProgramCounter),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn jump_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            JUMP(LocalSymbol(4, "symbol".to_string())),
            POP,
            PUSHC(Value::I32(2)),
            UOp(UnaryOp::NEG, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut symbols: SymbolTable = HashMap::new();
        symbols.insert("symbol".to_string(), 4);
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn jump_test_2() {
        let insts = vec![
            JUMP(UnresolvedSymbol("symbol".to_string())),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn djump_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::IPtr(5)),
            DJUMP(Source::Stack(0)),
            POP,
            PUSHC(Value::Void),
            UOp(UnaryOp::NEG, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn djump_test_2() {
        let insts = vec![
            PUSHC(Value::I32(0)),
            DJUMP(Source::Stack(0)),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn brancheq_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::Bool(true)),
            PUSHC(Value::Bool(true)),
            BRANCHEQ(Source::Stack(1), Source::Stack(0), LocalSymbol(6, "symbol".to_string())),
            POP,
            PUSHC(Value::Void),
            UOp(UnaryOp::NEG, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut symbols: SymbolTable = HashMap::new();
        symbols.insert("symbol".to_string(), 6);
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn brancheq_test_2() {
        let insts = vec![
            PUSHC(Value::Void),
            PUSHC(Value::Bool(true)),
            PUSHC(Value::Bool(false)),
            BRANCHEQ(Source::Stack(0), Source::Stack(1), LocalSymbol(6, "symbol".to_string())),
            POP,
            PUSHC(Value::I32(-1)),
            UOp(UnaryOp::NEG, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut symbols: SymbolTable = HashMap::new();
        symbols.insert("symbol".to_string(), 6);
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(1));
    }

    #[test]
    fn brancheq_test_3() {
        let insts = vec![
            PUSHC(Value::Void),
            PUSHC(Value::Bool(true)),
            PUSHC(Value::I32(1)),
            BRANCHEQ(Source::Stack(1), Source::Stack(0), LocalSymbol(6, "symbol".to_string())),
            POP,
            PUSHC(Value::I32(-1)),
            UOp(UnaryOp::NEG, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut symbols: SymbolTable = HashMap::new();
        symbols.insert("symbol".to_string(), 6);
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(1));
    }

    #[test]
    fn branchne_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::Bool(true)),
            PUSHC(Value::Bool(true)),
            BRANCHNE(Source::Stack(1), Source::Stack(0), LocalSymbol(6, "symbol".to_string())),
            POP,
            PUSHC(Value::I32(-1)),
            UOp(UnaryOp::NEG, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut symbols: SymbolTable = HashMap::new();
        symbols.insert("symbol".to_string(), 6);
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(1));
    }

    #[test]
    fn branchne_test_2() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::Bool(true)),
            PUSHC(Value::Bool(false)),
            BRANCHNE(Source::Stack(0), Source::Stack(1), LocalSymbol(6, "symbol".to_string())),
            POP,
            PUSHC(Value::I32(-1)),
            UOp(UnaryOp::NEG, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut symbols: SymbolTable = HashMap::new();
        symbols.insert("symbol".to_string(), 6);
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn branchne_test_3() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::Bool(true)),
            PUSHC(Value::I32(1)),
            BRANCHNE(Source::Stack(1), Source::Stack(0), LocalSymbol(6, "symbol".to_string())),
            POP,
            PUSHC(Value::I32(-1)),
            UOp(UnaryOp::NEG, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut symbols: SymbolTable = HashMap::new();
        symbols.insert("symbol".to_string(), 6);
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn branchon_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::Bool(true)),
            BRANCHON(Value::Bool(true), LocalSymbol(5, "symbol".to_string()), Source::Stack(0)),
            POP,
            PUSHC(Value::Void),
            UOp(UnaryOp::NEG, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut symbols: SymbolTable = HashMap::new();
        symbols.insert("symbol".to_string(), 5);
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(-1));
    }

    #[test]
    fn branchon_test_2() {
        let insts = vec![
            PUSHC(Value::Void),
            PUSHC(Value::Bool(true)),
            BRANCHON(Value::Bool(false), LocalSymbol(5, "symbol".to_string()), Source::Stack(0)),
            POP,
            PUSHC(Value::I32(-1)),
            UOp(UnaryOp::NEG, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut symbols: SymbolTable = HashMap::new();
        symbols.insert("symbol".to_string(), 5);
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(1));
    }

    #[test]
    fn branchon_test_3() {
        let insts = vec![
            PUSHC(Value::Void),
            PUSHC(Value::Bool(true)),
            BRANCHON(Value::I32(1), LocalSymbol(5, "symbol".to_string()), Source::Stack(0)),
            POP,
            PUSHC(Value::I32(-1)),
            UOp(UnaryOp::NEG, Destination::Stack(0), Source::Stack(0)),
        ];
        let mut symbols: SymbolTable = HashMap::new();
        symbols.insert("symbol".to_string(), 5);
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn loadfrom_test_1() {
        let insts = vec![
            PUSHC(Value::I32(2)),
            PUSHR(RegisterName::StackPointer),
            LOADFROM(Destination::Stack(0), Source::Stack(0)),
            BOp(BinaryOp::ADD, Destination::Stack(0), Source::Stack(1), Source::Stack(0)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(4));
    }

    #[test]
    fn loadfrom_test_2() {
        let insts = vec![
            PUSHC(Value::I32(2)),
            PUSHC(Value::I32(1)),
            LOADFROM(Destination::Stack(0), Source::Stack(0)),
            BOp(BinaryOp::ADD, Destination::Stack(0), Source::Stack(1), Source::Stack(0)),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }

    #[test]
    fn storeto_test_1() {
        let insts = vec![
            PUSHC(Value::I32(1)),
            PUSHC(Value::I32(1)),
            PUSHC(Value::I32(0)),
            PUSHC(Value::SPtr(0x1)),
            STORETO(Source::Stack(1), Source::Stack(0)),
            BOp(BinaryOp::ADD, Destination::Stack(0), Source::Stack(1), Source::Stack(0)),
        ];
        let mut thread = Thread::new(insts);
        assert_eq!(thread.exec().unwrap().unwrap(), Value::I32(1));
    }

    #[test]
    fn storeto_test_2() {
        let insts = vec![
            PUSHC(Value::I32(2)),
            PUSHC(Value::I32(1)),
            STORETO(Source::Stack(0), Source::Stack(1)),
        ];
        let mut thread = Thread::new(insts);
        assert!(thread.exec().is_err());
    }
}