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

