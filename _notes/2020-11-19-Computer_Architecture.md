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
Make processing instructions deep. Different stages. You need to stall the pipeline sometimes
Better throughput, worse latency

## [Hazards](https://en.wikipedia.org/wiki/Hazard_(computer_architecture))
Data
interrupts are an interesting one you can forget about, because they are so implciit

Control hazards
[Branch prediction](https://en.wikipedia.org/wiki/Branch_predictor)

## superscalar
Make processor wide, multiple pipelines.
Parallelism is decided at runtime. Check for data dependencies



## Out of order execution
[Scoreboard](https://en.wikipedia.org/wiki/Scoreboarding)


## [VLIW](https://en.wikipedia.org/wiki/Very_long_instruction_word)
pushes scheduling to compile time. Removes lots of complicated scheduling circuitt
Software pipelining vs Loop unrolling
Trace scheduling 

equal scheduling model - when does operation finish? Exactly at its latency
less-equal scheduling

# EPIC 

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


