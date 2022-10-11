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
    - [RISC V](#risc-v)
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
https://www.xorpd.net/pages/links.html

[yasm](http://yasm.tortall.net/)
nasm
fasm https://board.flatassembler.net/

[terse](http://www.terse.com/)
command line flag

## Debuggers
I've come to realize that even forplaying around in assmbly, a debugger is pretty clutch

- gdb - See notes in C.
- [cemu](https://github.com/hugsy/cemu) an ide of sorts for writing assembly and running it
- [ollydbg]
- [edb](https://github.com/eteran/edb-debugger) an ollydbg for linux. Seems nice. A graphical debugger.
- [x64dbg](https://github.com/x64dbg/x64dbg) windows only

## Directives
[gas](https://ftp.gnu.org/old-gnu/Manuals/gas-2.9.1/html_chapter/as_7.html) gas directives

- `.equiv`
- cfi directives
- `.debug_line` maps addresses to source code lines
- `.debug_info` maps source variables to registers and stack locations
- `.eh_frame` maps address location return address and callee saved registers info. "exception handling"

# x86
De facto standard for desktops

[intel software develpoer manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)

https://en.wikipedia.org/wiki/INT_(x86_instruction) int3 is a breakpoint instruction 
https://twitter.com/pkhuong/status/1507790343151960073?s=20&t=GsM8M-fHdbvp9M4n5S4-kg
## BMI1 BMI2
Bit manipulation instructions https://twitter.com/geofflangdale/status/1502481857375793153?s=20&t=j5MN13cFOkc3qH8tpATyNA
apparently people can do crazy stuff with this https://twitter.com/pkhuong/status/1497332651891515395?s=20&t=j5MN13cFOkc3qH8tpATyNA

pshufb 
pext
pdep


## GAS
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
## nasm

```edb
global _start
_start:
  mov rdi, 10 ; mov 10 into rdi.
  int3   ; interrupt for debugger
  add rsi, rdi ; 
  ret
```






## memory barrier
## CET control enforcement technology
`endbr` valid jump destinations for indirect jumps

x86 forth 

# ARM

Arm memory tagging extension

### RISC V
[risc v J extesnions](https://news.ycombinator.com/item?id=30647151)


https://www.cs.cornell.edu/courses/cs3410/2019sp/riscv/interpreter/# nice little interpeter to play with
[risc v from scratch](https://twilco.github.io/riscv-from-scratch/2019/04/27/riscv-from-scratch-2.html)


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
https://marz.utk.edu/my-courses/cosc230/book/example-risc-v-assembly-programs/

  * [https://www.chiark.greenend.org.uk/~sgtatham/coroutines.html](https://www.chiark.greenend.org.uk/~sgtatham/coroutines.html)
  * https://en.wikibooks.org/wiki/X86_Assembly
  * https://en.wikibooks.org/wiki/Embedded_Systems
  * https://www.ic.unicamp.br/~pannain/mc404/aulas/pdfs/Art%20Of%20Intel%20x86%20Assembly.pdf Art of Assembly DOS version. Good stuff in here. Some ways of implementing function calls I'd never considered

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

https://github.com/nanochess/bootBASIC boot sector basic
https://nanochess.org/
https://www.lulu.com/shop/oscar-toledo-gutierrez/programming-boot-sector-games/paperback/product-24188564.html?page=1&pageSize=4  <https://nanochess.org/store.html> programming boot sector games


sectorlisp

x86 forth 

[easy 6502 assembly](https://news.ycombinator.com/item?id=31548311) in browser assembler an emulator ebook



[Some Assembly Required](https://github.com/hackclub/some-assembly-required) https://news.ycombinator.com/item?id=31909183

[typed assembly language](https://www.cs.cmu.edu/~crary/papers/2003/talt/talt.pdf)