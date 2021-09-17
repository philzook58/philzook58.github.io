---
author: philzook58
comments: true
date: 2020-11-19 15:49:32+00:00
layout: post
link: https://www.philipzucker.com/?p=2995
published: false
slug: Computer Architecture - Assembly
title: Computer Architecture - Assembly
wordpress_id: 2995
---

https://cs.lmu.edu/~ray/notes/gasexamples/ Seems like really good intro to assembly

Hacking:
http://langsec.org/papers/Bratus.pdf sergey weird machine paper
smashing the stack for fun and profit - stacks are no longer executable
return to libc https://en.wikipedia.org/wiki/Return-to-libc_attack - libc is very common and
you can weave together libc calls. "Solar Designer"
https://en.wikipedia.org/wiki/Return-to-libc_attack
https://acmccs.github.io/papers/geometry-ccs07.pdf geometry of innocent flesh on the bone. ROP
http://phrack.org/issues/61/6.html advanced doug lea malloc hacking
https://github.com/sashs/Ropper
https://github.com/sashs/filebytes
http://www.capstone-engine.org/ - disassembler. converse of key
blackhat
defcon
bluehat
ccc
https://en.wikipedia.org/wiki/Security_BSides bsides
ctf
project zero
kpaersky blog https://usa.kaspersky.com/blog/
spectre/meltdown
mattermost gce8
https://www.youtube.com/watch?v=b7urNgLPJiQ&ab_channel=PinkDraconian

return oriented programming sounds like my backwards pass.
Huh.


example risc5 programs. sort, search. vector matrix mult, string copy.
https://marz.utk.edu/my-courses/cosc230/book/example-risc-v-assembly-programs/

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

Fun old timey books. If you go before 1980, a decent chunk of all books had assembly in mind.

  * discpline of programming - djikstra https://seriouscomputerist.atariverse.com/media/pdf/book/Discipline%20of%20Programming.pdf
  * Reynolds - The craft of programming
  * Knuth - The Art of Computer Programming
  * The science of programming - D Gries
  * Pascal, wirth
  * structured programming https://seriouscomputerist.atariverse.com/media/pdf/book/Structured%20Programming.pdf djikstra hoare
  * Eric Hehner
  * https://dl.acm.org/collections/classics ACM classic books
  * lambda papers
  * per brinch hansen
  * https://en.wikipedia.org/wiki/List_of_important_publications_in_theoretical_computer_science#Formal_verification
  * https://en.wikipedia.org/wiki/List_of_important_publications_in_computer_science
  * http://www.mathmeth.com/read.shtml some welevant EQD notes. Derivation of alogrithms
  * winskel 

  
I could write an interpreter in assembly. Knuth does it. Or I could write an asbtract machine CEK or something?

The stack is a linked list. It has pointers to the previous base pointer locations.   I found a stack overflow answer that was saying the stack and heap have constant, n, and ln n complexity for different operations. ... Wait. Is that right? Why does the heap have ln n?

Wengert tape vs stack. We could partially evaluate in some sense the wengert tapeto be interleaved with the code that sets up and tears down stack frames

f(g(x),h(y)) in terms of assembly lays out a traversal of the structure.

It seems like we could use 2 stacks maybe. One for regualr functions stuff and one to record backwards pass information. Primop lens.

How does one do nondeterminsitc search in assembly?

