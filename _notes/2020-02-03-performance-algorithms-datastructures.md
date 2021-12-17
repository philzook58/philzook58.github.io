---
layout: post
title: Performance, Algorithms
---

## Easyperf
Performance matters, it unlocks new applications, important for business
python -> avx extensions: x60,000 in one example
Measurement is really important and hard.
CPU can overclock for a little bit. Try to control the environment

## Agner Fog
###  manual 1
Reduce data dependencies
a[i++] may be faster than a[++i] because of a data dependency reduction
bool in C++ outputs 0/1 but may have come from a source that didn't. This means it needs branching code for simple satuff
short circuiting && ||, try to short circuit early



## Stuff

<https://twitter.com/lemire/status/1461181871841320962?s=20> Lemire converting integerrs to fix digit representations
By considering data dependencies and using lookup tables take from 25ns to 2ns.


See also
- Computer Architecture
- Assembly

MIT optimization course <https://ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-172-performance-engineering-of-software-systems-fall-2018/>


<https://news.ycombinator.com/item?id=29107147> <https://randomascii.wordpress.com/2012/12/29/the-surprising-subtleties-of-zeroing-a-register/> surprising subtleites of zeroing a register.

<https://www.agner.org/optimize/> agner fog optimization manuals

<https://twitter.com/nadavrot/status/1464364562409422852?s=20> memset and memcpy ooptimizations

<https://twitter.com/PieCalculus/status/1464252793225678850?s=20> Go does not need a garbage collector. Compares and contrasts java GC with others. Claims Java poorly designed make high pressure on GC

<https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html>
<https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-optimization-manual.pdf> intel opimization manual

<https://twitter.com/pervognsen/status/1455409607426207744?s=20> mimalloc- de moura, daan leijen, ben zorn
<https://lobste.rs/s/4awecj/mimalloc_free_list_sharding_action>
<https://github.com/microsoft/snmalloc/blob/c5b65d07b8079b22eec9f78bec197ea7a0fd15f2/difference.md>

I feel like most algorithms and data structures are os ordinary they are kind of boring?


Sparse Sets - knuth - bitvectors + 
Bitvectors  http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.681.8766&rep=rep1&type=pdf
ullmann bitvector algos for binary constraint and subgraph iso.

Books:
CLRS


Sorting algorithms
Hash tables
Dynamic programming
Tries
Graph algorithsm - shortest path, spanning tree

https://news.ycombinator.com/item?id=26590234#26592091 hash table in C. some interesting commments too
linear search - an assoc list but he kept it in an array
http://burtleburtle.net/bob/hash/doobs.html - hashing from z3 source code
https://craftinginterpreters.com/hash-tables.html

lkinear probing vs linked list in hash table. 

concurrent hash map


What this?
https://branchfree.org/2019/02/25/paper-parsing-gigabytes-of-json-per-second/
https://news.ycombinator.com/item?id=24069530
roaring bitmaps
simdjson
judy arrays
People are mentioned warming up the branch predictors on purpose somehow
Branchless programming

https://algorithmica.org/en/eytzinger https://news.ycombinator.com/item?id=26695694
Interesting. Cache-oblivious binary search. Uses the "Heap" ordering or what have you
Plus a branchless comparator?
I think also a big point is 
How do you even know when cache something is a problem. How do you use feedback and self correct?
How do you organize tight loops? "smart" ways of keeping structure.


microbenchmarking
performance counters - cache misses, TLB ht/miss, mispredicted branches
nanobench https://arxiv.org/pdf/1911.03282.pdf
VTune, perf, PAPI, libpfc,

What every programmer should know abouyt memory
https://people.freebsd.org/~lstewart/articles/cpumemory.pdf

modern microprcessor 90 minute guide
http://www.lighterra.com/papers/modernmicroprocessors/


https://en.wikipedia.org/wiki/Program_optimization
Bentley Writing Efficient Program


<https://news.ycombinator.com/item?id=28955461> - a rust optimization story
<https://pvk.ca/Blog/2012/07/03/binary-search-star-eliminates-star-branch-mispredictions/> 
<https://dirtyhandscoding.wordpress.com/2017/08/25/performance-comparison-linear-search-vs-binary-search/>
<https://www.youtube.com/watch?v=1tEqsQ55-8I&ab_channel=MollyRocket> - handmade hero guy talkin about optimizations
<https://www.youtube.com/watch?v=pgoetgxecw8&ab_channel=MollyRocket> - refterm optimization talk. this is fascinating

1. optimization - measuring.
2. non-pessimization - don't do unnecessary work
3. fake optimziation - people just repeatin shit


<https://www.uops.info/>
<https://uica.uops.info/> uica online demo gives info on what's hurtin ya. Cycle counts and stuff
microp_ops. Ports? Queue?
DaY 112 of hnadmade hero. perf counter. simd. converting to simd. measuring port usage with iaca

perf seems balla. Works on ocaml btw <https://ocaml.org/learn/tutorials/performance_and_profiling.html>
<https://www.brendangregg.com/perf.html>
<https://www.youtube.com/watch?v=fhBHvsi0Ql0&ab_channel=USENIX> - linux systems performance



https://www.gem5.org/ The gem5 simulator is a modular platform for computer-system architecture research, encompassing system-level architecture as well as processor microarchitecture
https://ieeexplore.ieee.org/document/8718630?denied=  gem5, MARSS×86 , Multi2Sim, PTLsim, Sniper, and ZSim.
gem5 as an alternaitve to qemu? http://www.diva-portal.org/smash/get/diva2:1058030/FULLTEXT01.pdf


https://www.infoq.com/presentations/microarchitecture-modern-cpu/

NUMA - non uniform memory access
register file? 
l1 cache. instruction and data. instruction is one way
`lstopo --no-io` tells you how your computer looks
large /huge pages. faster for TLB. Hugetablefs is linux suppotrt? `/proc/cpuinfo`
Transparent Huge Pages- `madvise` is a call yes I'd like huge tables. `defer`
cache lines - 64 bytes. even if you read/write 1 byte your're writing 64
M exculsively own and dirty, E exlucsive and clean, S shared, , I invalid
__builtin_prefecth_. linear access is good
splitting into revcord of arrays tends to be better for cache if only using one field. compressed memory is worth it. compuitayion is fast. memory is slow. Array of structs vs struct of arrays. Compressed pointers? https://en.wikipedia.org/wiki/Tagged_pointer https://v8.dev/blog/pointer-compression
pinning
`isolcpus` boot time option. pinning of thread or memory to cpu `taskset`. linux admin styuff. isolate cpus to certain tasks `numactl` and `libnuma`
loop stream decoder
branch predictor, pipelikne stall or bubble. 
branch target predcitro
ports, execution units. some logic, some airthmetic. 
`perf` - interrogate counters. `record report annotate stat`
skid - bad - precision knobs :p :pp :ppp    perf record -b perf record --call-graph lbr -j any_call,any_ret program -e intel_pt//u
LBR - last branch record - linux weekly  https://lwn.net/Articles/680985/ intel processors record control flow
Intel processor trace
IPC - intrcutions per cycle. 4 is maximum ish. less than 1 is  perf stat
performance ocunters - `perf -list`
`TMAM` top down microarctecture analsyis method `perf -dtopdown`
`toplev` go throgyh process. and kleen. fancy frontend to perf/ `-l1` `l2`
`__builtin_expect` 
profile guided optimization may do builtin expect for you
loop alginment - 32 bit boundaries. straight from uop cache. llvm flag. align-all-nofallthru-blocks  align-all-function 
https://easyperf.net/blog/2018/01/18/Code_alignment_issues code alignment can changed your perfoamnce.
BOLT - vinary optimization layout tranformer. defrag your code. Puts hot code in same memory location at runtime
Daniel Lemire - simd parser. mechnisms for avodiing branching. masking operations. 
Summary - cache aligned / cache aware data structures. B-trees. Compress data. Avoid random memory access. Huge pages can help. 10% speedup by enabling maybe. libnuma source memory. branch0free and lock-free. perf /toplev. Use vectorization where you  can. 
https://alblue.bandlem.com/ his blog
https://speakerdeck.com/alblue/understanding-cpu-microarchitecture-for-performance?slide=62 reference
https://speakerdeck.com/alblue/understanding-cpu-microarchitecture-for-performance?slide=63 links

Blog links neato: 
https://easyperf.net/notes/
https://epickrram.blogspot.com/
https://lemire.me/blog/
http://psy-lob-saw.blogspot.com/
https://richardstartin.github.io/
https://travisdowns.github.io/
https://www.agner.org/optimize/
https://www.real-logic.co.uk/
https://groups.google.com/g/mechanical-sympathy

