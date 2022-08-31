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