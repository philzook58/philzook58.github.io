---
author: philzook58
comments: true
date: 2020-11-19 15:49:32+00:00
layout: post
link: https://www.philipzucker.com/?p=2995
slug: Computer Architecture / Assembly
title: Computer Architecture / Assembly
wordpress_id: 2995
---

<https://ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-823-computer-system-architecture-fall-2005/lecture-notes/>
<https://www.youtube.com/c/OnurMutluLectures/playlists> Onur Mutlu lectures, courses
Should I do Gem5, verilog, vhdl, other?


Verilog I guess

icarus verilog is an easy enough to use simulator.

```verilog
module foo;
  initial begin
        $display("hi");
        $finish;
        end
endmodule //foo
```

Comments are //
initial is not even a statement. What syntactic category is it?
The prduced file is a vvp textfile

bitvectors are described in a very odd way. [lastbitindex:firstbitindex]


Architecture

arch vs microarch


data types and size
addresses
packed vector data
fp - cray, intel extended

isa
fixed - mips arm
variable length - x86 1-18bytes
compressed - thumb
vliw

nmber of operands

reg-reg
reg-mem



https://arxiv.org/pdf/1911.03282.pdf nanobench
https://developer.amd.com/amd-uprof/ amd uprof
https://people.freebsd.org/~lstewart/articles/cpumemory.pdf what every programmer should know baout memory


Hennessey and patterson

agner fog

intel optimization manual https://software.intel.com/sites/default/files/managed/9e/bc/64-ia-32-architectures-optimization-manual.pdf

architecture -  

  * [https://www.chiark.greenend.org.uk/~sgtatham/coroutines.html](https://www.chiark.greenend.org.uk/~sgtatham/coroutines.html)
  * https://en.wikibooks.org/wiki/X86_Assembly
  * https://en.wikibooks.org/wiki/Embedded_Systems
  * https://www.ic.unicamp.br/~pannain/mc404/aulas/pdfs/Art%20Of%20Intel%20x86%20Assembly.pdf Art of Assembly DOS version. Good stuff in here. Some ways of implementing function calls I'd never considered



  
I could write an interpreter in assembly. Knuth does it. Or I could write an asbtract machine CEK or something?

The stack is a linked list. It has pointers to the previous base pointer locations.   I found a stack overflow answer that was saying the stack and heap have constant, n, and ln n complexity for different operations. ... Wait. Is that right? Why does the heap have ln n?

Wengert tape vs stack. We could partially evaluate in some sense the wengert tapeto be interleaved with the code that sets up and tears down stack frames

f(g(x),h(y)) in terms of assembly lays out a traversal of the structure.

It seems like we could use 2 stacks maybe. One for regualr functions stuff and one to record backwards pass information. Primop lens.

How does one do nondeterminsitc search in assembly?

