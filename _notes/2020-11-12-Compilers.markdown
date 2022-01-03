---
author: philzook58
comments: true
date: 2020-11-12 20:17:39+00:00
layout: post
link: https://www.philipzucker.com/?p=2913
published: true
slug: Compilers
title: Compilers
wordpress_id: 2913
---

[esolang VM](https://github.com/shinh/elvm) - C compiler to simple virtual machine for compiling to esolangs

[Loop invariant code motion](https://en.wikipedia.org/wiki/Loop-invariant_code_motion) - aka hoisting. Move stuff that doesn't change out of the loop

[instruction level parallelism](https://link.springer.com/book/10.1007/978-1-4899-7797-7) Alex Aiken Utpal Banerjee Arun Kejariwal Alexandru Nicolau

Reassociate to lessen tree height - less dependencies
Expand expressions with care - less dependencies

[Polyhedral model](https://en.wikipedia.org/wiki/Polytope_model)
[Foundations of Fine Grain Parallelism](https://www.cs.colostate.edu/~cs560/Fall2015/). Recurrence equations. Analyze them
[granulairty](https://en.wikipedia.org/wiki/Granularity_(parallel_computing)) 

<https://jonathan2251.github.io/lbd/index.html>  Tutorial: Creating an LLVM Backend for the Cpu0 Architecturehttps://danielkeep.github.io/tlborm/book/README.html

<https://lowlevelbits.org/how-to-learn-compilers-llvm-edition/> - interesting links <https://twitter.com/1101_debian/status/1456346324794806274?s=20>
<https://news.ycombinator.com/item?id=29112482> more links
<https://www.youtube.com/watch?v=m8G_S5LwlTo&ab_channel=LLVM> LLVM IR tutorial
<cs.au.dk/~amoeller/spa> static program analysis

modules - global symbols, function declaration, function definitions, target information


<https://www.llvm.org/docs/ProgrammersManual.html>
<https://mukulrathi.com/create-your-own-programming-language/llvm-ir-cpp-api-tutorial/>


<https://gist.github.com/MattPD/00573ee14bf85ccac6bed3c0678ddbef> program analysis resources. Big long list.

http://ssabook.gforge.inria.fr/latest/book.pdf SSA bookv

Dataflow analysis
Must/May and intersection vs union. Least fixed point vs greatest
Is datalog actually a good fit
https://tudelft-cs4200-2020.github.io/ - hmm sppoofax
https://www.youtube.com/watch?v=Qp3zfM-JSx8&ab_channel=ACMSIGPLAN - souffle
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.648.1834&rep=rep1&type=pdf - reps
Engler 96

Man souffle does seem cool

  * [https://github.com/aalhour/awesome-compilers](https://github.com/aalhour/awesome-compilers)
  * [https://www.cs.cornell.edu/~asampson/blog/llvm.html](https://www.cs.cornell.edu/~asampson/blog/llvm.html)
  *   * [https://gcc.gnu.org/wiki/ListOfCompilerBooks](https://gcc.gnu.org/wiki/ListOfCompilerBooks)



It's surprisingly difficult to find a cogent explanation of all the stuff one might need. It's useful to call C or be called from C **https://blog.packagecloud.io/eng/2016/04/05/the-definitive-guide-to-linux-system-calls/**


    
    <code>	.globl compute_42
    compute_42:
        movq    %rdi, %rax # move argument into rax
    	addq	$32, %rax # add 32 
    	retq
        
    
    #include <stdio.h>
    #include <stdint.h>
    
    extern uint64_t compute_42(uint64_t a);
    
    int main()
    {
        printf("result is %ld \n", compute_42(4));
        return 0;
    }</code>


Making a simple garbage collector [https://maplant.com/gc.html](https://maplant.com/gc.html)


The boehm garbage collector sweems easy to use. Also you can just malloc and never free.


sjklsfkjl https://cs.brown.edu/courses/cs033/docs/guides/x64_cheatsheet.pdf x86 cheatsheet


alignment is for serious. It really does screw you if you don't do function alls with stack on 16byte boundaries


[https://en.wikibooks.org/wiki/X86_Assembly](https://en.wikibooks.org/wiki/X86_Assembly)


[https://modernc.gforge.inria.fr/](https://modernc.gforge.inria.fr/) modern c book free online


%rdi, %rsi, %rdx, %rcx, %r8, and %r9 as first 6 arguments


pushq %rbx is usually first instruction inside function


subq somethign rsp usually happens to allocate on the stack


[https://brown-cs0330.github.io/website/index.html](https://brown-cs0330.github.io/website/index.html) introduction to computer systems

Bryant and OHallaran book. CMU course http://www.cs.cmu.edu/~213/schedule.html

[https://bernsteinbear.com/blog/lisp/](https://bernsteinbear.com/blog/lisp/)

gdb. Compile with -g flag. break main. step next print. tui enabe https://sourceware.org/gdb/onlinedocs/gdb/TUI-Commands.html#TUI-Commands cheatsheet https://darkdust.net/files/GDB%20Cheat%20Sheet.pdf https://brown-cs0330.github.io/website/docs/guides/vgg.pdf

objdump -d -S -l

valgrind and core dumps.
