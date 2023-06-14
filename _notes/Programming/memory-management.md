---
layout: post
title: Memory Management
---


Memory management is like, important
https://en.wikipedia.org/wiki/Memory_management

# Stack
https://en.wikipedia.org/wiki/Stack-based_memory_allocation

alloca

# Malloc
[cool viualization of malloc](https://news.ycombinator.com/item?id=36029087)

# Pools
https://en.wikipedia.org/wiki/Memory_pool 
Object pools 
Thread pools
Fixed size block allocation
Can use `Vec<Foo>` 
push and pop to free

# Regions
https://en.wikipedia.org/wiki/Region-based_memory_management

Arenas?
Deallocate all at once. Good for fragmentation too.
https://manishearth.github.io/blog/2021/03/15/arenas-in-rust/


https://dl.acm.org/doi/pdf/10.1145/3519939.3523443 fearless concurrency. domination rather than unique ownershp

[ghost cells](https://plv.mpi-sws.org/rustbelt/ghostcell/)

Mads Tofte and Jean-Pierre Talpin. 1997. Region-Based Memory Management. 

# Garbage Collection
[garbage colleciton handbook 2](https://news.ycombinator.com/item?id=35492307)
[](https://wingolog.org/archives/2022/12/11/we-iterate-so-that-you-can-recurse)
[semi space collector](https://wingolog.org/archives/2022/12/10/a-simple-semi-space-collector)

[Immix: A Mark-Region Garbage Collector with Space Efficiency, Fast Collection, and Mutator Performance](https://www.cs.utexas.edu/users/speedway/DaCapo/papers/immix-pldi-2008.pdf)
Conservative
Moving

generational

bump pointers

Mark and Sweep

Boehm garbage collector

https://twitter.com/sickeningsprawl/status/1560817828411936770?s=20&t=5ByjIVPCy80__MKWdWW1Aw liballocs. Garbage collector that looks at dwarf data. Asiprataional?

[memory management toolkit](https://www.mmtk.io/)

[malloc and free are bad apis](https://www.foonathan.net/2022/08/malloc-interface/#content) store unnecessary metadata, waste space


[DangZero: Efficient Use-After-Free Detection via Direct Page Table Access](https://download.vusec.net/papers/dangzero_ccs22.pdf)

[Untangling Lifetimes: The Arena Allocator](https://www.rfleury.com/p/untangling-lifetimes-the-arena-allocator)

Garbage Collection Handbook

[ Control Theory and Concurrent Garbage Collection ](https://twitter.com/MadhavJivrajani/status/1578778595581124609?s=20&t=0RcVYoA5aTg4AHeb5ncYzw) https://speakerdeck.com/madhavjivrajani/control-theory-and-concurrent-garbage-collection-a-deep-dive-into-the-go-gc-pacer

[automemcpy: A Framework for Automatic Generation of Fundamental Memory Operations](https://twitter.com/johnregehr/status/1566780383416537088?s=20&t=Ed04dBodGtW0kFSYL76bNQ)

https://github.com/mflatt/gc-demo
https://www.youtube.com/playlist?list=PLbdXd8eufjyVCrWF-obj8_BbyU5vEF8Jw


[treadmill gabrage collector of baker](https://news.ycombinator.com/item?id=32233472) http://www.cofault.com/2022/07/treadmill.html

[garbage collection handbook](https://gchandbook.org/ )
[lua wiki](http://wiki.luajit.org/New-Garbage-Collector#gc-algorithms_quad-color-optimized-incremental-mark-sweep)

real-time
concurrent
copying vs non-copying. Copying needs to adjust pointers. Can defragment
incremental - does the garbage collection need to happen all at once

bump allocation


## Conservative vs Exact

The boehm garbage collector seems easy to use. Also you can just malloc and never free.
https://en.wikipedia.org/wiki/Boehm_garbage_collector



## Parallel
## Concurrent
## mark and Sweep
colors mark finished, seen but children not finished.
white is unseen. black is swept. When finished anything white is no longer in use.
## Generational


Making a simple garbage collector [https://maplant.com/gc.html](https://maplant.com/gc.html)
