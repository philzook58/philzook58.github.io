
<https://learnxinyminutes.com/docs/mips/>

Introduction to 80x86 Assembly Language and Computer Architecture" by R. C. Detmer, 2.
ed. 2006.

boot sector means they got the code under 512 bytes

https://github.com/nanochess/bootBASIC boot sector basic
https://nanochess.org/
https://www.lulu.com/shop/oscar-toledo-gutierrez/programming-boot-sector-games/paperback/product-24188564.html?page=1&pageSize=4  <https://nanochess.org/store.html> programming boot sector games


sectorlisp

x86 forth 
### RISC V
https://www.cs.cornell.edu/courses/cs3410/2019sp/riscv/interpreter/# nice little interpeter to play with



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


<https://cs.lmu.edu/~ray/notes/gasexamples/> Seems like really good intro to assembly


example risc5 programs. sort, search. vector matrix mult, string copy.
https://marz.utk.edu/my-courses/cosc230/book/example-risc-v-assembly-programs/