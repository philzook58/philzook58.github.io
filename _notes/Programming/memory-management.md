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

# Garbage Collection
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
