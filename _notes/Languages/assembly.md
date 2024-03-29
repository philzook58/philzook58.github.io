---
layout: post
title: Assembly
---

- [Assemblers](#assemblers)
  - [Debuggers](#debuggers)
  - [Directives](#directives)
- [x86](#x86)
  - [BMI1 BMI2](#bmi1-bmi2)
  - [GAS](#gas)
  - [nasm](#nasm)
  - [memory barrier](#memory-barrier)
  - [CET control enforcement technology](#cet-control-enforcement-technology)
- [ARM](#arm)
- [PowerPC](#powerpc)
- [RISC V](#risc-v)
- [6502](#6502)
- [VAX](#vax)
- [FORTH](#forth)
- [High level assemlby / macros](#high-level-assemlby--macros)
- [Typed Assembly](#typed-assembly)
- [Proof Carrying Code](#proof-carrying-code)
- [Verification](#verification)
- [Semantics / Specification](#semantics--specification)
- [Misc](#misc)

See also nots on:

- computer architecture
- performance
- linkers

`-S` flag on gcc and other compilers often dumps assembly
Godbolt compiler explorer is also very useful

# Assemblers

gas - gnu assembler
[llvm-as](https://llvm.org/docs/CommandGuide/llvm-as.html)
<https://www.xorpd.net/pages/links.html>

[yasm](http://yasm.tortall.net/)
nasm
fasm <https://board.flatassembler.net/>

[terse](http://www.terse.com/)
command line flag

[SASM - simple crossplatform IDE for NASM, MASM, GAS and FASM assembly languages](https://github.com/Dman95/SASM) <http://dman95.github.io/SASM/>

Macro-11 <https://en.wikipedia.org/wiki/MACRO-11> PDP-11 macro assembly. Interesting [manual](http://bitsavers.trailing-edge.com/pdf/dec/pdp11/rsx11m_s/RSX11M_V2/DEC-11-OIMRA-A-D_MACRO_75.pdf)

## Debuggers

See note on debuggers

I've come to realize that even forplaying around in assmbly, a debugger is pretty clutch

## Directives

[gas](https://ftp.gnu.org/old-gnu/Manuals/gas-2.9.1/html_chapter/as_7.html) gas directives

- `.equiv`
- cfi directives
- `.debug_line` maps addresses to source code lines
- `.debug_info` maps source variables to registers and stack locations
- `.eh_frame` maps address location return address and callee saved registers info. "exception handling"

# x86

<https://blog.jeff.over.bz/assembly/compilers/jit/2017/01/15/x86-assembler.html>  x86 assembler in 250 lines of C

De facto standard for desktops

[intel software develpoer manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)

<https://en.wikipedia.org/wiki/INT_(x86_instruction)> int3 is a breakpoint instruction
<https://twitter.com/pkhuong/status/1507790343151960073?s=20&t=GsM8M-fHdbvp9M4n5S4-kg>

[asmtutor](https://asmtutor.com/)

[box64](https://github.com/ptitSeb/box64) x86 emultator for arm
[fex](https://fex-emu.com/)

[x86 gui programming](https://news.ycombinator.com/item?id=36153237)
using strace is kind of cool

[say hello to x86 assembly](https://github.com/0xAX/asm)

- `mov` `movz` `movs`
- `movsb` copy byte from esi to edi and inc/dec both. Useful string op
- `cmov__` conditional mov based on flags.
- `lea` calculates a pointer offset in one instruction. 3 operands, a shift and a constant add.
- `add` `sub` `or` `xor` `inc` `dec`
- `imul` `idiv` `mul`. one parameter. implicit rax as one operand. rdx:rax as implicit output
- `syscall`
- `test` `cmp` <https://stackoverflow.com/questions/39556649/in-x86-whats-difference-between-test-eax-eax-and-cmp-eax-0>
- `jmp` `jnz` `jz` condition suffixes
- `setxx` copy from flags
- `call`
- `push` `pop` `enter` `leave`
- `loop` kind of a goofball. dec ecx and jump if zero. [Hmm slow?](https://stackoverflow.com/questions/35742570/why-is-the-loop-instruction-slow-couldnt-intel-have-implemented-it-efficiently)

[x86 assembly book](https://en.wikibooks.org/wiki/X86_Assembly)

Addressing modes

`rdi, rsi, rdx, rcx, r8-r11, rax` are all good scratch registers. The first 6 of those are where function arguments go. rax is where return values go

rax accumulatr, rcx counter, rdx extended accumulator, rbx base of array,  <https://en.wikipedia.org/wiki/X86#Purpose>

## BMI1 BMI2

Bit manipulation instructions <https://twitter.com/geofflangdale/status/1502481857375793153?s=20&t=j5MN13cFOkc3qH8tpATyNA>
apparently people can do crazy stuff with this <https://twitter.com/pkhuong/status/1497332651891515395?s=20&t=j5MN13cFOkc3qH8tpATyNA>

pshufb
pext
pdep

## GAS

Using qemu is nice even on native because we can use `-d` flag to dump cpu state and instruction. Then I dn't have to fiddle wth gdb or a gui or include printf functionlity or remember system call numbers for call / calling conventions. All great stuff, but annoying if you're interested in just fiddling with assembly.

```bash
echo '
#include <sys/syscall.h>
.extern _start
_start:
    mov $0x20,%rax
    int3 # interrupt. execution will stop here. analog of printf debugging
    mov $0x42,%rax
    mov $60, %rax # exit syscall number for clean exit. or just let it segfault. yolo.
    syscall
    int $0x80
    #int3
' > /tmp/myprog.s
gcc -nostdlib -static -o /tmp/myprog /tmp/myprog.s
qemu-x86_64 -d in_asm,cpu -singlestep /tmp/myprog

```

<https://cs.lmu.edu/~ray/notes/gasexamples/> Seems like really good intro to assembly
<https://jameshfisher.com/2018/03/10/linux-assembly-hello-world/>

```x86
.global _start
.data
hello:
  .ascii "Hello world\n"
  len = . - hello
.text
_start:
  mov $1, %rax # write
  mov $1, %rdi # stdout
  mov $hello, %rsi #
  mov $len, %rdx
  syscall

  mov $60, %rax #  exit
  mov $0, %rdi
  syscall

```

using a macro

```x86
.global _start
.macro myprint str len
  mov $1, %rax # write
  mov $1, %rdi # stdout
  mov \str, %rsi
  mov \len, %rdx
  syscall
.endm

.data
hello:
  .ascii "Hello world\n"
  len = . - hello
.text
_start:
  myprint $hello, $len

  mov $60, %rax #  exit
  mov $0, %rdi
  syscall

```

Using a function. RDI, RSI, RDX, RCX, R8, R9

```x86
.global _start
.text
myprint:
  mov %rsi, %rdx   #len
  mov %rdi, %rsi
  mov $1, %rax  # write
  mov $1, %rdi  # stdout
  syscall
  ret
_start:
  mov $hello, %rdi
  mov $len, %rsi
  call myprint

  mov $60, %rax #  exit
  mov $0, %rdi
  syscall
.data
hello:
  .ascii "Hello world\n"
  len = . - hello

```

```bash
echo '
.global _start
_start:
  mov $0x42, %rax
  int3
' | as -o /tmp/a.out #-x assembler -
ld /tmp/a.out -o /tmp/a2.out
#chmod +x /tmp/a.out
gdb /tmp/a2.out -ex run -ex 'info registers'

```

## nasm

<https://www.nasm.us/doc/>

Nasm does seem a little nicer. x86 only though.

[nasm tutorial](https://cs.lmu.edu/~ray/notes/nasmtutorial/) pretty good

```edb
global _start
_start:
  mov rdi, 10 ; mov 10 into rdi.
  int3   ; interrupt for debugger
  add rsi, rdi ; 
  ret
```

- `db` pseduo instruction

```bash
echo "
global _start
section .text
_start:
  mov rax, 42
  int3
" > /tmp/test.s
nasm -felf64 /tmp/test.s -o /tmp/temp
ld /tmp/temp -o /tmp/temp2
file /tmp/temp2
gdb /tmp/temp2
```

```bash
echo "
;default rel
extern puts
global main
section .text
main:
  sub rsp, 8
  mov BYTE [rsp + 0], 'h'
  mov BYTE [rsp + 1], 'e'
  mov BYTE [rsp + 2], 'l'
  mov BYTE [rsp + 3], 'l'
  mov BYTE [rsp + 4], 'o'
  mov BYTE [rsp + 5], 0
  mov rdi, rsp
  CALL puts WRT ..plt

  mov rax,0
  add rsp,8
  ret

" > /tmp/test.s
nasm -felf64 /tmp/test.s -o /tmp/temp
gcc /tmp/temp  -o /tmp/temp2
file /tmp/temp2
/tmp/temp2
```

[unix abi](https://gitlab.com/x86-psABIs) <https://github.com/hjl-tools/x86-psABI/wiki/X86-psABI/>

## memory barrier

## CET control enforcement technology

`endbr` valid jump destinations for indirect jumps

x86 forth

# ARM

<https://github.com/marcpaq/arpilisp> an arm lisp

[](https://github.com/pkivolowitz/asm_book)
Arm memory tagging extension

[cpulator](https://cpulator.01xz.net/?sys=arm) online assembler and emulator for teaching pretty nice
[Assembly Language Programming with ARM – Full Tutorial for Beginners](https://www.youtube.com/watch?v=gfmRrPjnEw4&t=1484s&ab_channel=freeCodeCamp.org)
[INTRODUCTION TO ARM ASSEMBLY BASICS - Azeria](https://azeria-labs.com/writing-arm-assembly-part-1/)

r7 is system call
`mov r0, #0xa`

```
mov r7, #1
swi 0

mov r2, r1


ldr r0,=mylist
ldr r0,[r0]
ldr r2,[r0,#4]
.data
mylist:
  .word 4,5,6,7,42
```

```python
import tempfile
import subproess
def asm(code):
  with tempfile.TemporaryFile() as fp:
    fp.write(code)
    fp.flush()
    subprocess.run(["arm-linux-gnueabi-as", fp.name])
    subprocess.run(["gdb", fp.name])




```

```python
from unicorn import *
mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)

```

[ARMv8 A64 Quick Reference](https://courses.cs.washington.edu/courses/cse469/19wi/arm64.pdf)
[](https://github.com/below/HelloSilicon)
[asm tutor port](https://github.com/lirorc/arm-asm-examples)

# PowerPC

# RISC V

[SAIL Risc V spec](https://github.com/riscv/sail-riscv)
[riscv- coq](https://github.com/mit-plv/riscv-coq)

[risc v J extesnions](https://news.ycombinator.com/item?id=30647151)
[graphical assembler and cpu emulator](https://github.com/mortbopet/Ripes)

<https://www.cs.cornell.edu/courses/cs3410/2019sp/riscv/interpreter/#> nice little interpeter to play with
[risc v from scratch](https://twilco.github.io/riscv-from-scratch/2019/04/27/riscv-from-scratch-2.html)
[A Multipurpose Formal RISC-V Specification](https://people.csail.mit.edu/bthom/riscv-spec.pdf) hs-2-coq based
[compcert risc-v backend](https://github.com/AbsInt/CompCert/tree/master/riscV)

[mini-rv32ima is a single-file-header riscv5 eumlator](https://github.com/cnlohr/mini-rv32ima)
[instruction decoder in javascript? Why?](https://luplab.gitlab.io/rvcodecjs/)

[risc v virtual machine](https://github.com/LekKit/RVVM)
[rvemu](https://github.com/d0iasm/rvemu) [Writing a RISC-V Emulator in Rust book](https://book.rvemu.app/)

```riscv
# it's the sum of 1 to n
addi a0, x0, 4
addi t0, x0, 0
addi t1, x0, 1
loop:
  add t0,a0,t0
  sub a0, a0, t1
  #jal x0, loop
  bne a0, x0, loop
```

<https://web.eecs.utk.edu/~smarz1/courses/ece356/notes/assembly/> notes

<https://github.com/jameslzhu/riscv-card/blob/master/riscv-card.pdf> nice cheatsheet of instructions, registers
registers

- a0 a1 are arguments nad returns values
- t0-t are temporaries
- x0 or zero is zero register
- equivalent floating point just add f.
- s0 .. saved resgiters

instructions

example risc5 programs. sort, search. vector matrix mult, string copy.
<https://marz.utk.edu/my-courses/cosc230/book/example-risc-v-assembly-programs/>

- [https://www.chiark.greenend.org.uk/~sgtatham/coroutines.html](https://www.chiark.greenend.org.uk/~sgtatham/coroutines.html)
- <https://en.wikibooks.org/wiki/X86_Assembly>
- <https://en.wikibooks.org/wiki/Embedded_Systems>
- <https://www.ic.unicamp.br/~pannain/mc404/aulas/pdfs/Art%20Of%20Intel%20x86%20Assembly.pdf> Art of Assembly DOS version. Good stuff in here. Some ways of implementing function calls I'd never considered

# 6502

<https://www.dabeaz.com/superboard/asm6502.py> 6502 assembler in python

# VAX

<https://en.wikipedia.org/wiki/VAX>
<https://news.ycombinator.com/item?id=38901012> vax in fpga
supposedly vax was a very nice assembly language. The ultimate cisc. Greg has mentioned some really cool macro programming abilities.

# FORTH

<https://en.wikipedia.org/wiki/Threaded_code>

- [Jonesforth](https://github.com/nornagon/jonesforth) super well annotated forth written in x86
<https://news.ycombinator.com/item?id=22801471>
- [moving forth series](https://www.bradrodriguez.com/papers/)
-

<https://en.wikipedia.org/wiki/Threaded_code>

<https://gitlab.com/tsoding/porth>

# High level assemlby / macros

<https://en.wikipedia.org/wiki/High-level_assembler>

The art of assembly book by Hyde

If, for, while macros
Auto flattening.
`(loc,asm)` pairs
`r0 == (r0, "")`

<https://github.com/nbenton/x86proved>
[Coq: The world’s best macro assembler?](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/coqasm.pdf)

# Typed Assembly

```bash
echo "
int foo(int x) {
  return x + 42;
}
" | gcc -g -x c -c -o /tmp/foo.o -
objdump -d /tmp/foo.o
```

```python
import angr
proj = angr.Project("/tmp/foo.o")
foo = proj.loader.find_symbol("foo")
cfg = proj.analyses.CFGFast()
#print(dir(proj))
print(dir(foo))
foo = cfg.kb.functions["foo"]
print(foo)
from pypcode import Context, PcodePrettyPrinter
ctx = Context("x86:LE:64:default")
dx = ctx.disassemble(b"\x48\x35\x78\x56\x34\x12\xc3")
for ins in dx.instructions:
    print(f"{ins.addr.offset:#x}/{ins.length}: {ins.mnem} {ins.body}")
  
print(dir(foo))
```

Type preserving compilation
Shift from alpha bound names to true names.
`foo: {ebx:b4}` label `foo` expects a 4 byte value in `ebx`
They still have a code rewriting semantics analagous to immediate subtition.
Closures use existential types

Code blocks have type annotations about assumptions of typed content of registers
code pointers
stacks have type sequences and polymorphic below that.

[weirich papers we love](https://www.youtube.com/watch?v=Epbaka9uTQ4&ab_channel=PapersWeLovePhiladelphia)

related to PCC (proof carryng code). Use type discipline

The continuation is carried on the stack (typically). {eax:b4} is the calling convention on x86. {rax:b8} would be calling convention on x86_64. That continuation is threaded through everything (if we don't smash stack)

A summation program annotated

```
sum: ; {ecx:b4, ebx:{eax:b4}}
  mov eax, 0  ; int acc = 0;
  jmp test
loop:{eax:b4, ecx:b4, ebx:{eax:b4}}
  add eax, ecx  ; acc += x
  dec ecx      ; x--;
  ; FALLTHRU
test: ; {eax:b4, ecx:b4, ebx:{eax:b4}}
  cmp ecx,0 ; while( x != 0)
  jne loop 
  jmp ebx ; return acc
```

Compare and contrast these annotations with preconditions. I mean, types can be viewed as some kind of abstract interpretation.

[tal weirich haskell](https://github.com/sweirich/tal)

[FunTAL: reasonably mixing a functional language with assembly](https://dl.acm.org/doi/10.1145/3062341.3062347) [prncipled language interopaibility course - ahmed](https://www.ccs.neu.edu/home/amal/course/7480-s19/) [](https://dbp.io/pubs/2022/dbp-dissertation.pdf)
[TAL website](https://www.cs.cornell.edu/talc/)
[TALx86]()
[from system f to typed assembly language](https://www.cs.princeton.edu/~dpw/papers/tal-toplas.pdf)
[typed assembly language](https://www.cs.cmu.edu/~crary/papers/2003/talt/talt.pdf)
[alasteir reid's notes](https://alastairreid.github.io/RelatedWork/papers/morrisett:wcsss:1999/)

[stack based tpyed assembly language](http://trac.parrot.org/parrot/raw-attachment/wiki/LoritoCPSTutorial/stal-tic.pdf)
Stack type: esp sptr to a stack
`forall rho:Ts. {esp:sptr{eax:B4, esp:sptr B4::rho}::B4::rho”`

Using "free theorem" to ensure callee register saving.
`forall a. {r0:'a, r1:{r0:'a} }` the only way to type this is to pass r0 into the contuation.
Analog of `forall b, b -> (b -> Void) -> Void`. Security / noniterference and polymorphism free theorems are the same kind of thing

[Type-Based Decompilation1 (or program reconstruction via type reconstruction)](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=91043faf9894af4c85c53343c702085daed73d42) hmm. datalog disassembly as type reconstruction?

Can I embed TAL as a well typed DSL in ocaml staged metaprograming style? Polymorphic record types would probably be nice. I mean, it's possible that's what they already did?

```ocaml
type sem = string
type (a,b) stack
{ void
type eax
type edx
type ecx
type 'a fptr

(* "subtyping" using polymorphism *)
type ('r0, 'r1, 'r2) regfile = {r0 : 'r0; r1 : 'r1; r2 : 'r2 }

let zero_reg : (int,int,int) regfile = {r0 = 0; r1 = 0; r2 = 0}
let r0_valid : ( int  , ?  , ? ) regfile (* existential type maybe?  (forall r1 r2. (int, r1,r2) regfile -> 'ret) -> 'ret *)

type 
type instr = Mov 

let rec interp heap regfile instr = 
  match instr with
  | Jump nu ->
  | Mov dst src -> 
  | Add dst src1 src2 ->
  | If cond dst fall -> 



(* analogous to metaocaml's code *)
type 't asm = string
let assemble : 't asm -> 't =
    let bin = Unix.exec ["as" ; ] in
    let = Unix.mmap Execute yada
    let f = ccall
    Obj.magic 

let disassemble : 't -> 't asm (* ?? *) =
    (* use obj to figure out code pointer. Differentiate code pointers vs closures. *)
    let Unix.exec "objdump" or "ghidra" ???

let compile : 't code -> 't asm = 
    let Unix.exec "ocamlopt"

let decompile : 't asm -> 't code = 

let byte_compile : 't code -> 't bytecode = 
    let Unix.exec "ocamlc"
  
```

```ocaml

(*Might want to go objects just for strucutral notaton *)
(* let mov_r0_r1 : < r0 : 'a; r1: 'b> -> <r0 : 'a; r1 : 'a> = fun st -> *)

(* 
type ('r0, 'r1, 'r2) st = ST
let mov_r0_r1 : ('r0,'r1,'r2) st -> ('r0, 'r0, 'r2) st = fun x -> ST
*)

(* let mov : 'rdst reg -> 'rsrc reg ->  
   Ths can't work at all
   selection style?
   (a,b,c) reg -> (a1,b1,c1) reg -> ? 
   
  
COuld first class modules help? I don't really see it.

module type INSN = sig


end

*)







(* let mov : 'a reg -> 'b reg -> {rax : } *)
```

```ocaml

(* het list *)
type ('xs, 'x) cons = {hd : 'x; tl : 'xs} 
type nil = unit
let cons x xs = {hd = x; tl = xs}
let nil = ()

let swap : type r. ((r, 'b) cons, 'a) cons -> ((r, 'a) cons, 'b) cons = 
  fun x -> cons x.tl.hd (cons x.hd x.tl.tl)
let binop : ('a -> 'b -> 'c) ->  (('r, 'b) cons, 'a) cons -> ('r, 'c) cons   = 
  fun op st -> cons (op st.hd st.tl.hd) st.tl.tl

let add = binop (+)
let sub = binop (-)
let mul = binop (fun x y -> x * y)

let push : 'a -> 'r -> ('r, 'a) cons = cons
let imm = push
let pop : ('r, 'a) cons -> 'r = fun st -> st.tl
let dup : ('r, 'a) cons -> (('r, 'a) cons, 'a) cons = fun st -> cons st.hd st  


module type STACKSIG = sig
  type 'a repr
  type ('xs, 'x) cons
  type nil
  (* list out types supported *)
  (* Hmm. I dunno if that raw 'r is ok. *)
  val push_int : int repr -> 'r -> ('r, int) cons
end



(* use rdi,...  etc as extensions of the stack?
   Mark extra param
   *)
type rdi = RDI
type rsi = RSI
type rax = RAX

(*
type ('rdi, 'rsi) regfile = {rdi : 'rdi ; rsi : 'rsi}

   *)

(* 
consider the stack below arguments as non existent... hm.
let systemv_call_1 : ( (nil , 'a , rdi) cons -> ('b, rax) cons) -> ('a -> 'b)  
   
Or we could just mov regusters onto the stack as a prelude
Or internaly track not in types what is around.

type ( , ) cons = {hd : location ; ty : 'x;   in_use :   }

*)


```

So what is the type of `mov rax, 0`? How is fallthru represented?

TAL led in some ways to Cyclone, which is turn heavily influenced rust

What would a "well-typed" interpreter of assembly look like
Mem, Reg ->

Pierce - Advanced Topics has a chapter on TAL and PCC (4 and 5)

[Ulf norell typed assembly in agda](https://github.com/UlfNorell/x86-agda/blob/master/src/Test.agda)

<https://twitter.com/search?q=typed%20assembly&src=typed_query> twitter

[chen and hawblitzel - channel 9 introduction to typed assembly. Verse a typed operatiog system](https://web.archive.org/web/20211126000658/https://sec.ch9.ms/ch9/6f8d/5edac2dc-adcc-4b2e-93b7-9ecc016c6f8d/MSRTypedAssemblyLanguage_low_ch9.mp4)
[Safe to the last instruction: automated verification of a type-safe operating system](https://dl.acm.org/doi/10.1145/1809028.1806610) - Verve a type safe operating system
[Hawblitzel bibliography](https://dblp.org/pid/22/3053.html)

[xi and harper - a dependently typed assembly langguae](https://www.cs.cmu.edu/~rwh/papers/dtal/icfp01.pdf)
[singleton 2011- a depently typed assembly langguae](https://dl.acm.org/doi/10.1145/1929553.1929557)

[Inferable object-oriented typed assembly language - Tate Chen hawblitzel](https://dl.acm.org/doi/10.1145/1806596.1806644) [youtube](https://www.youtube.com/watch?v=HjdA3W6Mg-c&t=252s&ab_channel=RossTate)

```prolog
% pcode
% tabled prolog appropriate becase we need unification variables for polymorphism.
hastype() :- .


```

dwarf annotations as untrusted input?

gradual typing is a natural fit
[dynamic typed assembly languge](https://digitalcommons.usf.edu/cgi/viewcontent.cgi?article=8230&context=etd)

# Proof Carrying Code

foundational pcc - appell and felty
[A Tutorial Example of the Semantic Approach to Foundational Proof-Carrying Code](https://link.springer.com/chapter/10.1007/978-3-540-32033-3_29)
Chapter in Pierce
[Necula's thesis](https://www.cs.princeton.edu/~appel/proofsem/papers/necula-thesis.ps)

[INTERFACING COMPILERS, PROOF CHECKERS, AND PROOFS FOR FOUNDATIONAL PROOF-CARRYING CODE- Wu thesis](https://faculty.ist.psu.edu/wu/papers/wu-phd-thesis.pdf) annotation are untrusted.

LF
metamath0
ebpf connection?

# Verification

[Verified Transformations and Hoare Logic: Beautiful Proofs for Ugly Assembly Language](https://link.springer.com/chapter/10.1007/978-3-030-63618-0_7)
Galois' SAW
[A verified, efficient embedding of a verifiable assembly language](https://dl.acm.org/doi/10.1145/3290376)
F* land. [Vale - Verifying High-Performance Cryptographic Assembly Code](https://project-everest.github.io/assets/vale2017.pdf). Hmm. this is leveraging dafny

# Semantics / Specification

[L3 in cakeml](https://cakeml.org/itp22-armv8.pdf)
[L3 risc v](https://github.com/SRI-CSL/l3riscv/tree/master)
[L3 mips](https://github.com/acjf3/l3mips)

[alastair reid's notes](https://alastairreid.github.io/RelatedWork/notes/isa-specification/)

Sail
ASL arm spec language

[A Complete Formal Semantics of x86-64 User-Level Instruction Set Architecture](https://fsl.cs.illinois.edu/publications/dasgupta-park-kasampalis-adve-rosu-2019-pldi.pdf) K framework

[Flexible Instruction-Set Semantics via Type Classes](https://arxiv.org/pdf/2104.00762.pdf)

[risc v Machine Readable Specs](https://five-embeddev.com/quickref/machine-readable.html)

```bash
echo "
default Order dec // what does this do?
\$include <prelude.sail>

//val print = monadic {ocaml: \"print_endline\"} : string -> unit

let n:int = 42
// val myguy

//function myguy(x) = x + 1
enum E = A | B | C

//val main : unit -> unit

function main (() : unit) -> unit = print_endline(\"hello world\")
" > /tmp/foo.sail
sail -coq -o /tmp/foo /tmp/foo.sail 
cat /tmp/foo.v
```

`sail -i` interpreter

<https://github.com/rems-project/isla/blob/master/doc/manual.adoc>
isla. It's more than a symbolic executor
I can dump an IR of instruction semantics. Pseudo-smt. Has command statements too. Still. The expressions are smt expressions yea?

[pydrofoil](https://github.com/pydrofoil/pydrofoil) using pypy jit with sail. It uses isla to dump semantics?

# Misc

[bootstrapping a c compiler](https://news.ycombinator.com/item?id=31244150)
<https://learnxinyminutes.com/docs/mips/>

[bootsector games](https://gist.github.com/XlogicX/8204cf17c432cc2b968d138eb639494e)
Introduction to 80x86 Assembly Language and Computer Architecture" by R. C. Detmer, 2.
ed. 2006.

[xorpd](https://www.xorpd.net/index.html)
[xchg rax rax](https://www.xorpd.net/pages/xchg_rax/snip_00.html)
[reversing hero](https://www.reversinghero.com/)
[flatassembler](http://flatassembler.net/)

boot sector means they got the code under 512 bytes

<https://github.com/nanochess/bootBASIC> boot sector basic
<https://nanochess.org/>
<https://www.lulu.com/shop/oscar-toledo-gutierrez/programming-boot-sector-games/paperback/product-24188564.html?page=1&pageSize=4>  <https://nanochess.org/store.html> programming boot sector games

sectorlisp

x86 forth

[easy 6502 assembly](https://news.ycombinator.com/item?id=31548311) in browser assembler an emulator ebook

[Some Assembly Required](https://github.com/hackclub/some-assembly-required) <https://news.ycombinator.com/item?id=31909183>

Metamath zero - is there some simpler thing one could do? Why did metamath _really_ have to be written in assembly? Is this a trusted computing base thing?

[peachpy](https://github.com/Maratyszcza/PeachPy) an assembly dsl in python
<https://docs.micropython.org/en/latest/pyboard/tutorial/assembler.html> inline assembler in micropython
