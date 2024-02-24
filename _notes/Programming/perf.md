---
layout: post
title: Performance
---

- [Profiling](#profiling)
- [Estimating Maximum Possible Perf](#estimating-maximum-possible-perf)
- [Instruction Level Parallelism (ILP)](#instruction-level-parallelism-ilp)
- [SIMD](#simd)
- [Memory](#memory)
  - [Power](#power)
  - [Cache](#cache)
  - [Page](#page)
- [Resources](#resources)
  - [Easyperf](#easyperf)
  - [Agner Fog](#agner-fog)
    - [manual 1](#manual-1)
  - [Stuff](#stuff)
- [People](#people)

See Also:

- compilers
- computer architecture
- operating systems
- assembly
- parallel
- concurrency
- ebpf
- fuzzing

# Profiling

I mean. This is the whole name of the game really.

<https://thume.ca/2023/12/02/tracing-methods/> All my favorite tracing tools: eBPF, QEMU, Perfetto, new ones I built and more - Tristan Hume

Intel PT
ebpf

# Estimating Maximum Possible Perf

If compute bound: Single core freq ~3Ghz * 8 byte words -> 24Gb/s
RAM
SSD speeds - look it up. sequential vs no nsequential v different. Maybe ~1 gb/s as a order of magnitude

Network

[latency numbers every programmer should know](https://colin-scott.github.io/personal_website/research/interactive_latency.html)
[napkin math](https://www.youtube.com/watch?v=IxkSlnrRFqc)

<https://twitter.com/lemire/status/1746276695030600182> estimating memory bandwidth <https://lemire.me/blog/2024/01/13/estimating-your-memory-bandwidth/>

What kind of stuff is in _my_ cpu. How to estimate various parameters.

```bash
lscpu -C # cache
#NAME ONE-SIZE ALL-SIZE WAYS TYPE        LEVEL SETS PHY-LINE COHERENCY-SIZE
#L1d       48K     192K   12 Data            1   64        1             64
#L1i       32K     128K    8 Instruction     1   64        1             64
#L2       512K       2M    8 Unified         2 1024        1             64
#L3         8M       8M   16 Unified         3 8192        1             64

lscpu -e
#CPU NODE SOCKET CORE L1d:L1i:L2:L3 ONLINE    MAXMHZ   MINMHZ      MHZ
#  0    0      0    0 0:0:0:0          yes 3900.0000 400.0000 1500.000
#  1    0      0    1 1:1:1:0          yes 3900.0000 400.0000 1500.000
#  2    0      0    2 2:2:2:0          yes 3900.0000 400.0000 1500.000
#  3    0      0    3 3:3:3:0          yes 3900.0000 400.0000 1500.000
#  4    0      0    0 0:0:0:0          yes 3900.0000 400.0000 1500.000
#  5    0      0    1 1:1:1:0          yes 3900.0000 400.0000 1500.000
#  6    0      0    2 2:2:2:0          yes 3900.0000 400.0000 2719.516
#  7    0      0    3 3:3:3:0          yes 3900.0000 400.0000 2873.892

#  Address sizes:         39 bits physical, 48 bits virtual
# Vulnerabilities. That's ineresting
```

<https://en.wikichip.org/wiki/intel/core_i7/i7-1065g7>  my cpu
Max 55.63 GiB/s Bandwidth Single 13.91 GiB/sDouble 27.82 GiB/sQuad 55.63 GiB/s

# Instruction Level Parallelism (ILP)

# SIMD

<https://news.ycombinator.com/item?id=38443253> <https://mcyoung.xyz/2023/11/27/simd-base64/> Designing a SIMD Algorithm from Scratch

[Filtering a vector with simd - rust](https://quickwit.io/blog/filtering%20a%20vector%20with%20simd%20instructions%20avx-2%20and%20avx-512/)

[art of simd - slotkin](https://www.youtube.com/watch?v=vIRjSdTCIEU)

<https://arxiv.org/abs/2306.00229> Minotaur: A SIMD-Oriented Synthesizing Superoptimizer

<https://dl.acm.org/doi/10.1145/3372297.3423352> HACLxN: Verified Generic SIMD Crypto (for all your favourite platforms)

<https://simdjson.org/>
<https://roaringbitmap.org/> compressed bitmaps

<http://0x80.pl/notesen/2023-04-09-faster-parse-ipv4.html>

[Simd for C++ developers](http://const.me/articles/simd/simd.pdf)

What this?
<https://branchfree.org/2019/02/25/paper-parsing-gigabytes-of-json-per-second/>
<https://news.ycombinator.com/item?id=24069530>
roaring bitmaps
simdjson
judy arrays
People are mentioned warming up the branch predictors on purpose somehow
Branchless programming

```bash
"
#include <chrono>
#include <thread>
#include <vector>
#include <cstdint>
#include <iostream>

volatile size_t g_sum = 0;
__attribute__ ((noinline))
uint64_t sum(const uint8_t *data, size_t start, size_t len, size_t skip = 1) {
    uint64_t sum = 0;
    for (size_t i = start; i < len; i+= skip) {
        sum += data[i];
    }
    g_sum += sum;
    return sum;
}
" 


```

<https://github.com/cmuratori/blandwidth>
<https://github.com/MattPD/cpplinks/blob/master/performance.tools.md#memory---benchmarking>

<https://www.intel.com/content/www/us/en/developer/articles/tool/intelr-memory-latency-checker.html> intel memory latency checker

# Memory

See also note on memory-management

dhat check for memory allocation sites that are worst
<https://en.wikipedia.org/wiki/Memory_pool>
<https://en.wikipedia.org/wiki/Object_pool_pattern>
Can use vector to store fixed size chunks. Your own private malloc specialized for one size
<https://en.wikipedia.org/wiki/Slab_allocation>

memory overhead. Probably Powers of two. But allocator may have "slop" can lose a lot of memory that way

What every programmer should know about memory <https://people.freebsd.org/~lstewart/articles/cpumemory.pdf>

RAM -
DDR <https://en.wikipedia.org/wiki/Synchronous_dynamic_random-access_memory> double data rate.
read cycle time - time between reads tosame row
CAS latency - time from column to recieving data

RAS, CAS, WE bits select command type

Cache lines - 64 bytes. Even if you read/write 1 byte you're writing 64

## Power

Power profiling is determining what is using electricity / battery life up.
Very relevant to my common problem with my laptop dying

<https://firefox-source-docs.mozilla.org/performance/#power-profiling>

powertop <https://access.redhat.com/documentation/en-us/red_hat_enterprise_linux/8/html/monitoring_and_managing_system_status_and_performance/managing-power-consumption-with-powertop_monitoring-and-managing-system-status-and-performance>

<https://wiki.archlinux.org/title/Laptop_Mode_Tools>

Hmm.
wifi is using a lot of power

intel_atomic_commit - huh. is this actually correlated with touching the touchpad?
<https://community.frame.work/t/tracking-touchpad-interrupts-battery-usage-issues-idma64-2/13630>

nic:docker0 is using a lot.
sudo systemctl disable docker.service
sudo ifconfig docker0 down
sudo ifconfig br-557a6ccfc9fc down

A mysterious br-something device is usng like 5W of power. <https://askubuntu.com/questions/814316/how-to-determine-identity-of-obscure-nicbr-devices-in-powertop?rq=1>
INternet still works if I turn that off

hrtimer_wakeup

## Cache

## Page

<https://www.computerenhance.com/p/powerful-page-mapping-techniques>
[how to allocate huge tables](https://twitter.com/trascendentale/status/1462916354453946371?s=20&t=p3cq_31MG7DBts7HVR_-lg)

# Resources

## Easyperf

Performance matters, it unlocks new applications, important for business
python -> avx extensions: x60,000 in one example
Measurement is really important and hard.
CPU can overclock for a little bit. Try to control the environment

Use statistical tests to determine if real change. student t for example
Plot your benchmark data. Bimodal? Two different behaviors are happening
microbenchmarks: be careful. Is it inlining a bunch of stuff? Anything except your exact final application and environment is a proxy. That the proxy at all represents the real behavior is fishy. Never forget that.
System clock and system counters.

## Agner Fog

### manual 1

Reduce data dependencies
a[i++] may be faster than a[++i] because of a data dependency reduction
bool in C++ outputs 0/1 but may have come from a source that didn't. This means it needs branching code for simple satuff
short circuiting && ||, try to short circuit early

## Stuff

<https://github.com/google/highway> Performance-portable, length-agnostic SIMD with runtime dispatch

<https://x.com/ashvardanian/status/1759819906160480651?s=20> <https://github.com/ashvardanian/StringZilla> <https://github.com/unum-cloud/ucall> <https://github.com/unum-cloud/usearch>

rust perf book <https://nnethercote.github.io/perf-book/title-page.html>

Intel PT
LBR

 1 billion row challenge 1brc <https://twitter.com/search?q=1brc&src=typed_query> <https://github.com/gunnarmorling/1brc> <https://www.morling.dev/blog/one-billion-row-challenge/> <https://github.com/gunnarmorling/1brc/discussions/categories/show-and-tell>
 <https://news.ycombinator.com/item?id=39020906> remoe java unsafe

criterion <https://github.com/bheisler/criterion.rs>
<https://github.com/bheisler/iai> use cachegrind for stable measurements in CI
<https://github.com/sharkdp/hyperfine>  benchamrking commandline programs
<https://github.com/dandavison/chronologer> timeline over git commit

[casey muratori series](https://www.computerenhance.com/)

[cp algorithms](https://cp-algorithms.com/#navigation) competitive programming algorithsm

[geoff langdale blog](https://branchfree.org/)

[iterating over set bits](https://lemire.me/blog/2018/03/08/iterating-over-set-bits-quickly-simd-edition/)

[Computing Adler32 Checksums at 41 GB/s](https://news.ycombinator.com/item?id=32377597) <https://wooo.sh/articles/adler32.html>

[how fast are linux pipes anyway](https://mazzo.li/posts/fast-pipes.html)
pv - pipe viewer. pipe thorughput <http://www.ivarch.com/programs/pv.shtml>

really cool blog posts <https://mazzo.li/archive.html>

Software pipelining <https://twitter.com/geofflangdale/status/1531858991336550400?s=20&t=geOHu86_aPOLlcz-y8fE0Q>

The Art of Writing Efficient Programs: An advanced programmer's guide to efficient hardware utilization and compiler optimizations using C++ examples - Pikus

[Given the potential for straightline speculation w/ deleterious performance impact, does it makes sense to align functions with speculation blocking instructions like INT3 instead of nops?](https://twitter.com/pkhuong/status/1507790343151960073)
[microbenchmarks of return address prediction (ras)](https://blog.stuffedcow.net/2018/04/ras-microbenchmarks/)

[programming parallel computers course](https://ppc.cs.aalto.fi/)
`asm("# foo");` nice trick. Inject comment into assembly

[](https://blog.janestreet.com/magic-trace/)

[fread vs mmap](https://lemire.me/blog/2012/06/26/which-is-fastest-read-fread-ifstream-or-mmap/) Rough advice: fread is simple and often comparable to mmap (system dependent). mmap can sometimes be up to 4x faster, use madvise, weird exceptions/signals need to be handled.

[performance tuning on linux - cromwell](https://cromwell-intl.com/open-source/performance-tuning/)

[dan luu new cpu features](https://danluu.com/new-cpu-features/)

[Parsing series of integers with SIMD](http://0x80.pl/articles/simd-parsing-int-sequences.html) This [Wojciech Muła](http://0x80.pl/) guy is a wizard

[unaligned vector load + length-driven PSHUFB. What's everyone's favourite way to handle page crossings?](https://twitter.com/pkhuong/status/1497332651891515395?s=20&t=BoUiLAriWXha2_XgoVMl5A) overreading for short variables possibly into out of bounds memory? pshufb

[umash](https://github.com/backtrace-labs/umash) very fast hash
[Algorithms for Modern Hardware](https://github.com/sslotin/amh-code) - book on algorithms on modern hardware

[CLMUL](https://en.wikipedia.org/wiki/CLMUL_instruction_set) fast instruction set for galois field calculations. carryless

[x86 instrinsic cheatsheet](https://db.in.tum.de/~finis/x86-intrin-cheatsheet-v2.1.pdf)

[OSACA](https://github.com/RRZE-HPC/OSACA) an analyzer of assembly code. It is on godbolt

<iframe width="800px" height="200px" src="https://godbolt.org/e#g:!((g:!((g:!((h:codeEditor,i:(filename:'1',fontScale:14,fontUsePx:'0',j:1,lang:analysis,selection:(endColumn:12,endLineNumber:8,positionColumn:12,positionLineNumber:8,selectionStartColumn:12,selectionStartLineNumber:8,startColumn:12,startLineNumber:8),source:'square(int):%0A++++++++pushq+++%25rbp%0A++++++++movq++++%25rsp,+%25rbp%0A++++++++movl++++%25edi,+-4(%25rbp)%0A++++++++movl++++-4(%25rbp),+%25eax%0A++++++++imull+++%25eax,+%25eax%0A++++++++popq++++%25rbp%0A++++++++ret'),l:'5',n:'0',o:'Analysis+source+%231',t:'0')),k:50,l:'4',n:'0',o:'',s:0,t:'0'),(g:!((h:compiler,i:(compiler:osacatrunk,filters:(b:'0',binary:'1',commentOnly:'0',demangle:'0',directives:'0',execute:'1',intel:'1',libraryCode:'1',trim:'1'),flagsViewOpen:'1',fontScale:14,fontUsePx:'0',j:1,lang:analysis,libs:!(),options:'',selection:(endColumn:1,endLineNumber:1,positionColumn:1,positionLineNumber:1,selectionStartColumn:1,selectionStartLineNumber:1,startColumn:1,startLineNumber:1),source:1,tree:'1'),l:'5',n:'0',o:'OSACA+(0.4.7)+(Analysis,+Editor+%231,+Compiler+%231)',t:'0')),k:50,l:'4',n:'0',o:'',s:0,t:'0')),l:'2',n:'0',o:'',t:'0')),version:4"></iframe>

 This gruop has a number of interesting tools. <https://github.com/RRZE-HPC> It scrapes info from

- Likwid
- [kerncraft](https://github.com/RRZE-HPC/kerncraft) loop kernel analysis and performance modelling

[List of interesting optimizers](https://en.wikipedia.org/wiki/Optimizing_compiler) - These are compiler optimizations, so hopefully your compiler does them for you, but maybe it doesn't and maybe

<https://twitter.com/lemire/status/1461181871841320962?s=20> Lemire converting integerrs to fix digit representations
By considering data dependencies and using lookup tables take from 25ns to 2ns.

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
Bitvectors  <http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.681.8766&rep=rep1&type=pdf>
ullmann bitvector algos for binary constraint and subgraph iso.

Books:
CLRS

Sorting algorithms
Hash tables
Dynamic programming
Tries
Graph algorithsm - shortest path, spanning tree

<https://news.ycombinator.com/item?id=26590234#26592091> hash table in C. some interesting commments too
linear search - an assoc list but he kept it in an array
<http://burtleburtle.net/bob/hash/doobs.html> - hashing from z3 source code
<https://craftinginterpreters.com/hash-tables.html>

lkinear probing vs linked list in hash table.

concurrent hash map

<https://algorithmica.org/en/eytzinger> <https://news.ycombinator.com/item?id=26695694>
Interesting. Cache-oblivious binary search. Uses the "Heap" ordering or what have you
Plus a branchless comparator?
I think also a big point is
How do you even know when cache something is a problem. How do you use feedback and self correct?
How do you organize tight loops? "smart" ways of keeping structure.

microbenchmarking
performance counters - cache misses, TLB ht/miss, mispredicted branches
nanobench <https://arxiv.org/pdf/1911.03282.pdf>
VTune, perf, PAPI, libpfc,

What every programmer should know abouyt memory
<https://people.freebsd.org/~lstewart/articles/cpumemory.pdf>

modern microprcessor 90 minute guide
<http://www.lighterra.com/papers/modernmicroprocessors/>

<https://en.wikipedia.org/wiki/Program_optimization>
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

<https://www.gem5.org/> The gem5 simulator is a modular platform for computer-system architecture research, encompassing system-level architecture as well as processor microarchitecture
<https://ieeexplore.ieee.org/document/8718630?denied=>  gem5, MARSS×86 , Multi2Sim, PTLsim, Sniper, and ZSim.
gem5 as an alternaitve to qemu? <http://www.diva-portal.org/smash/get/diva2:1058030/FULLTEXT01.pdf>

<https://www.infoq.com/presentations/microarchitecture-modern-cpu/>

NUMA - non uniform memory access
register file?
l1 cache. instruction and data. instruction is one way
`lstopo --no-io` tells you how your computer looks
large /huge pages. faster for TLB. Hugetablefs is linux suppotrt? `/proc/cpuinfo`
Transparent Huge Pages- `madvise` is a call yes I'd like huge tables. `defer`
cache lines - 64 bytes. even if you read/write 1 byte your're writing 64
M exculsively own and dirty, E exlucsive and clean, S shared, , I invalid
__builtin_prefecth_. linear access is good
splitting into revcord of arrays tends to be better for cache if only using one field. compressed memory is worth it. compuitayion is fast. memory is slow. Array of structs vs struct of arrays. Compressed pointers? <https://en.wikipedia.org/wiki/Tagged_pointer> <https://v8.dev/blog/pointer-compression>
pinning
`isolcpus` boot time option. pinning of thread or memory to cpu `taskset`. linux admin styuff. isolate cpus to certain tasks `numactl` and `libnuma`
loop stream decoder
branch predictor, pipelikne stall or bubble.
branch target predcitro
ports, execution units. some logic, some airthmetic.
`perf` - interrogate counters. `record report annotate stat`
skid - bad - precision knobs :p :pp :ppp    perf record -b perf record --call-graph lbr -j any_call,any_ret program -e intel_pt//u
LBR - last branch record - linux weekly  <https://lwn.net/Articles/680985/> intel processors record control flow
Intel processor trace
IPC - intrcutions per cycle. 4 is maximum ish. less than 1 is  perf stat
performance ocunters - `perf -list`
`TMAM` top down microarctecture analsyis method `perf -dtopdown`
`toplev` go throgyh process. and kleen. fancy frontend to perf/ `-l1` `l2`
`__builtin_expect`
profile guided optimization may do builtin expect for you
loop alginment - 32 bit boundaries. straight from uop cache. llvm flag. align-all-nofallthru-blocks  align-all-function
<https://easyperf.net/blog/2018/01/18/Code_alignment_issues> code alignment can changed your perfoamnce.
BOLT - vinary optimization layout tranformer. defrag your code. Puts hot code in same memory location at runtime
Daniel Lemire - simd parser. mechnisms for avodiing branching. masking operations.
Summary - cache aligned / cache aware data structures. B-trees. Compress data. Avoid random memory access. Huge pages can help. 10% speedup by enabling maybe. libnuma source memory. branch0free and lock-free. perf /toplev. Use vectorization where you  can.
<https://alblue.bandlem.com/> his blog
<https://speakerdeck.com/alblue/understanding-cpu-microarchitecture-for-performance?slide=62> reference
<https://speakerdeck.com/alblue/understanding-cpu-microarchitecture-for-performance?slide=63> links

# People

Blog links neato:
<https://easyperf.net/notes/>
<https://epickrram.blogspot.com/>
<https://lemire.me/blog/>
<http://psy-lob-saw.blogspot.com/>
<https://richardstartin.github.io/>
<https://travisdowns.github.io/>
<https://www.agner.org/optimize/>
<https://www.real-logic.co.uk/>
<https://groups.google.com/g/mechanical-sympathy>
nethrcote blog <https://nnethercote.github.io/>
