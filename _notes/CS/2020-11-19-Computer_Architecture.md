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

See also note on:
- Concurrency

## Architecture Course

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



## pipelining
Like car assembly line
Make processing instructions deep. Different stages. You need to stall the pipeline sometimes
Better throughput, worse latency
Appendix C
classic 5 stage [RISC pipline](https://en.wikipedia.org/wiki/Classic_RISC_pipeline)
- Instruction fetch
- instruction decode
- execute
- Memory
- Write


## [Hazards](https://en.wikipedia.org/wiki/Hazard_(computer_architecture))
structural - if only have so many units that do a certain thing
Data
interrupts are an interesting one you can forget about, because they are so implicit

Control hazards
[Branch prediction](https://en.wikipedia.org/wiki/Branch_predictor)

## superscalar
Make processor wide, multiple pipelines.
Parallelism is decided at runtime. Check for data dependencies



## Out of order execution
[Scoreboard](https://en.wikipedia.org/wiki/Scoreboarding)
Is this where the idea of register file really comes into play?
To remember dependencies

## [VLIW](https://en.wikipedia.org/wiki/Very_long_instruction_word)
pushes scheduling to compile time. Removes lots of complicated scheduling circuitt
[Software pipelining](https://en.wikipedia.org/wiki/Software_pipelining) vs Loop unrolling. Sortware pipelining removes the loop head? No, software pipelining reorders the statements perhaps after a loop unroll to give dependencies space. We can also sort of reorganize the association of loop variable to statements 

Trace scheduling 

equal scheduling model - when does operation finish? Exactly at its latency
less-equal scheduling - can't pack something in that less than windoww anymore. The looawe the spec, the less ahead of time reeasonig we can do

compressed instructions

[predication](https://en.wikipedia.org/wiki/Predication_(computer_architecture))
partial predication - Conditional move instructions for example
full predication
avoid small chunks of branched code
When is computing both sides of a branch worth it? balanced or longest is frequently executed
The `it` instructions in arm


ALAT
code hammock

appendix H. 
Dependency analysis. The indices are 
[Loop dependence analysis](https://en.wikipedia.org/wiki/Loop_dependence_analysis)
I wonder if this is what llvm wants presburger for
True dependence - read after write
antidependance - write after read
output dependence- write after write

Use z3 for analysis

loop carried dependence
For going across loops we need to know the order. 
i <= i' dependence

antidependeance

### [branch prediction](https://en.wikipedia.org/wiki/Branch_predictor)
static prediction 0 Coin toss or just assuming fallthrough may work 50% of time
Alternative to delay slots. 2 delay slots can be hard to fill
Backwards jumps occur commonly in loops. More commonly taken than not taken
Hint flags in instructions - can be profiled to make better. Maybe %80 accuracy

1-bit predictor. did you most recently jump or not
n-bit history predictor - keep table
table based on jump address
Predictor is trained. A table is built
Time adn spatial correlation
Combinding methods - boosting. gets you to ~99% which you need for deep pipelines

predicting address of indirect jumps

EPIC

# Cache
associative cache
cache coherence
victim cache
write buffer
multi level cache
prefetching


# SMT - simultaneous multi threading
Intel hyperthreading
[TLBleed](https://www.blackhat.com/us-18/briefings/schedule/#tlbleed-when-protecting-your-cpu-caches-is-not-enough-10149/) programs hyperhtreading can side channel info to each other



dhrystone -benchmark suite. Patterson kind of rails on it.

delay slots - something that makes more sense when you're aware of microarchecture


https://arxiv.org/pdf/1911.03282.pdf nanobench
https://developer.amd.com/amd-uprof/ amd uprof
https://people.freebsd.org/~lstewart/articles/cpumemory.pdf what every programmer should know baout memory



<https://ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-823-computer-system-architecture-fall-2005/lecture-notes/>
<https://www.youtube.com/c/OnurMutluLectures/playlists> Onur Mutlu lectures, courses
Should I do Gem5, verilog, vhdl, other?


