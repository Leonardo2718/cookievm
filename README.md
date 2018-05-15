# The Cookie Virtual Machine

Cookie is a simple bytecode-based Virtual Machine (VM). Its aims to be:
easy to learn, easy to use, and generic. One of its intended uses is as
a target for educational compilers. Performance is not a priority for
this VM.

A quick highlight of some features:

- strongly dynamically typed
- can act as both a stack machine and a register machine
    - (see v-instructions)

## Type system

Cookie is strongly and dynamically typed. 

| Type name | Description |
|:----------|:------------|
| `I32`     | 32-bit integer
| `F32`     | IEEE-754 single word (32-bit) floating point
| `Char`    | Character type |
| `Bool`    | Boolean type
| `IPtr`    | Instruction address (pointer)
| `SPtr`    | Stack address (pointer)
| `Void`    | Unit type (only has one possible value `Void`)

## Values

Being dynamically typed, all values carry a type. Values are represented
by their type name followed by the value itself, surrounded by `(` and `)`.
All integer and floating point values are represented in decimal (base 10),
while all pointer types are represented in hexadecimal with a leading `0x`.
Characters must be surrounded by `'` (single quotation marks). The `Void`
type has, by definition, only one value called `Void`.

| Example value | Interpretation |
|:--------------|:---------------|
| `I32(3)`      | The integer 3
| `F32(3.14159` | The floating-point value 3.14159 (pi)
| `Char('c')`   | The character `c`
| `Bool(true)`  | Boolean value `true`
| `IPtr(0xabc)` | Instruction address `0xabc`
| `SPtr(0xdef)` | Stack address `0xdef`
| `Void`        | The value of the `Void` unit type

## Registers

Cookie supports of total of 16 General Purpose Registers (GPRs) and three
special registers that are used for managing the VM. The GPRs can contain
values of any type, while the special registers can only contain values of
a specific type. All register names start with a `$`.

| Register name | Type   | Description |
|:--------------|:-------|:------------|
| `$sp`         | `SPtr` | Stack pointer: points to top element on the stack |
| `$fp`         | `SPtr` | Frame pointer: points to base of current stack frame |
| `$pc`         | `IPtr` | Program counter: points to the current instruction |
| `$0` - `$15`  | any    | GPRs: 16 general purpose registers |

## The stack

The cookie stack grows up, meaning that the address stored in `$sp` increases
when a value is pushed onto the stack. The first stack slot has address `0x0`.
However, this slot is **not addressable**, meaning that the first usable stack
address is `0x1`. When the VM starts up, both `$sp` and `$fp` are initialized
to `0x0`. Stack slots can store values of any type and are initialized to
`Void` on VM startup. An important implication is that all values take up one
stack slot, no matter how many bytes are needed to store the value internally.
The difference between the addresses of two adjacent stack slots is therefore
always 1.

```
0x4 | I32(1)     | <- $sp
0x3 | SPtr(0x1)  |
0x2 | Bool(true) |
0x1 | F32(0.5)   |
0x0 | Void       | <- $fp (non-addressable)
```

## Instruction set

Currently the instruction set is very minimal. It provides just enough
functionality to be a useful compilation target.

The following tables list and describe the supported instructions.

| Instruction | Description |
|:------------|:------------|
| `PUSHR <r>` | Push content of register `<r>` onto the stack
| `PUSHC <v>` | Push constant value `<v>` onto the stack
| `POPR <r>`  | Pop value from the stack and put it in register `<r>`
| `POP`       | Pop value from the stack and discard it
| `JUMP <l>`  | Jump to (goto) label `<l>'
| `EXIT`      | End program execution
| `S.<vinst>` | Execute v-instruction `<vinst>` grabbing operands from the stack
| `R.<vinst>` | Execute v-instruction `<vinst>` grabbing operands from registers

### V-Instructions

V-Instructions (variable instructions) are those that can either use the stack
or registers for their operands. Which to use is determined by the prefix to the
instruction: `S.` for the stack and `R.` for registers. When the stack is used,
operands the right most-operands are popped first (i.e. operands must be pushed
left-to-right).

## Stack-frame (activation record) layout

Cookie does not enforce any particular calling convention or stack frame layout.
One possible activation record layout is shown bello:

```
| local n | <- %sp
|   ...   |
| local 1 |
| local 0 |
| return  | <- %fp
| link    |
| old fp  |
| arg n   |
|   ...   |
| arg 1   |
| arg 0   |
| void    |
```

