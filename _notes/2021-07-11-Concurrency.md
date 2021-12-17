---
author: philzook58
comments: true
date: 2020-11-20 19:07:10+00:00
layout: post
title: Concurrency
wordpress_id: 3009
---

<https://www.youtube.com/watch?v=N07tM7xWF1U&ab_channel=CppCon> abusing your memory model for fun and profit
<https://news.ycombinator.com/item?id=29109156> what memory model should rust use

John regehr thread https://twitter.com/johnregehr/status/1451355617583460355?s=20 Really good
https://mirrors.edge.kernel.org/pub/linux/kernel/people/paulmck/perfbook/perfbook.html  Is Parallel Programming Hard, And, If So, What Can You Do About It?
https://deadlockempire.github.io/
https://github.com/BIT-SYS/KDR list of kernel data races
Herlihy is discussed as a given? https://www.amazon.com/Art-Multiprocessor-Programming-Revised-Reprint/dp/0123973376
https://www.amazon.com/-/en/dp/0470093552 concurrency state models and jabva programsd
https://www.manning.com/books/c-plus-plus-concurrency-in-action-second-edition
https://leanpub.com/concurrencywithmodernc
https://greenteapress.com/wp/semaphores/ little book of semaphors
https://googleprojectzero.blogspot.com/2021/10/how-simple-linux-kernel-memory.html kernel memory corruption bug from data race prokject zero
Concurrent Programming (Andrews) -- uses pseudo-code with synchronization/concurrency notation.
Transactional Memory (Harris) -- for non-lock based concurrency.
https://lwn.net/Articles/844224/ an introduction to lockless algorithms 
"Shared-Memory Synchronization" by Michael Scott
https://herbsutter.com/2013/02/11/atomic-weapons-the-c-memory-model-and-modern-hardware/
http://plv.mpi-sws.org/gps/paper.pdf GPS: Navigating Weak Memory with Ghosts, Protocols, and Separation
Weak memory models?
https://pvk.ca/Blog/2019/01/09/preemption-is-gc-for-memory-reordering/ - 
https://pvk.ca/Blog/2020/07/07/flatter-wait-free-hazard-pointers/
https://www.cs.rochester.edu/u/scott/papers/1991_TOCS_synch.pdf algorithms for scababe synchronization on shared-memory. Same Michiael Scott. BBN butterfly?
https://arxiv.org/abs/1106.5730 HOGWILD - parallizingf lock free SGD
A Primer on Memory Consistency and Cache Coherence  https://course.ece.cmu.edu/~ece847c/S15/lib/exe/fetch.php?media=part2_2_sorin12.pdf
https://pure.tue.nl/ws/files/4279816/344354178746665.pdf cooperating seauentail prcoesses by dikstra
http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/concurrency.pdf ohearn resources concurrency and local reasoning
http://pascal.hansotten.com/uploads/pbh/Monitors%20and%20Concurrent%20Pascal.pdf monitors and concrurent pacscal hitsotry - per brinch hansen https://twitter.com/PeterOHearn12/status/1452240719725346827?s=20 " atomic "release and sleep" is the key as far as I'm concerned, it's so easy to invent bad solutions without that primitive"
https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.227.3871&rep=rep1&type=pdf the 12 commandments of synchrnonizatiojn


Concurrency
Mutex
Lock
Concurrent hash table https://en.wikipedia.org/wiki/Concurrent_hash_table
barriers

 https://www.youtube.com/watch?v=80ifzK3b8QQ&list=PL1835A90FC78FF8BE&index=1&ab_channel=BartoszMilewski - bartosz on c++11 concurrency

pthread vs std::thread
Arc in rust
condition variables

https://www.manning.com/books/c-plus-plus-concurrency-in-action-second-edition

https://www.coursera.org/learn/concurrent-programming-in-java


C++/Java/Ocaml memory models
https://github.com/herd/CoqCat - interesting thesis too
https://github.com/herd/herdtools7
https://github.com/ocamllabs/ocaml-memory-model
https://en.wikipedia.org/wiki/Memory_model_(programming) 
https://www.hboehm.info/c++mm/ hans boehm link farm - "impossible as a library"
http://www.cl.cam.ac.uk/~pes20/cpp/popl085ap-sewell.pdf - mathematizzing C++ memory model, kodkod, isabelle

Various kinds of relations.


futex - fats userspace mutex

 lockless algorithsm
https://lwn.net/Articles/844224/
MPI Cilk OpenMP

rust model checker actor system thing
https://www.stateright.rs/

Leslie lamport

Lindsey kuper has a dist sys course
It's probably pretty good
https://www.youtube.com/playlist?list=PLNPUF5QyWU8O0Wd8QDh9KaM1ggsxspJ31

Lecture 1. 
  several node,s connected by network, characterized by partial failure
cloud vs hpc
cloud
treat failure as expected and work around it "Eveerything fails all tyhe timne" - werner vogels
hpc- 
partial is total failure. checkpointing

M1 -> M2 x?
Posslbe problems:
1. lost request
2. request from M1 is slow
3. M2 crashes
4. M2 slow to respond
5. seponse is slow
6. response could get lost
7. corrupt - byzantine faults.

important: send request to another node and don't receive a response, it is impossible for you to know why

How do real systems cope?
Timeout - wait a certain amount of time then assume failure - imperfect solutuojn

max delay d. max process time r. cn't really do this
asynchronous network - no max 
Palvaro - partiasl failure + unbounded latency

https://people.ucsc.edu/~palvaro/ - dedalus - datalog in time and space. https://www.youtube.com/watch?v=R2Aa4PivG0g&ab_channel=StrangeLoopConference bloom blazes, data lineage multiple proofs are fault tolerant. lineage. Why did happen: produce explanation / proof. Cegis? concolic kind of? observability.

https://martin.kleppmann.com/  https://www.youtube.com/playlist?list=PLeKd45zvjcDFUEv_ohr_HdUFe97RItdiB

https://github.com/aphyr/distsys-class
https://www.distributedsystemscourse.com/

kyle kingsbury

chaos engineering - nora jones netflix

http://book.mixu.net/distsys/
https://www.youtube.com/watch?v=cQP8WApzIQQ&list=PLrw6a1wE39_tb2fErI4-WkMbsvGQk9_UB&ab_channel=MIT6.824%3ADistributedSystems


### Lecture 2 - kuper
clocks. scheduling. intervals in time
time of day clocks, monotonic clocks
NTP network time protocl. not so good for measuring inervals. can jump forward or backward
cloudflare leap second bug
monotonic - only goes forward

import time
time.monotonic() . not comparable between machines

logical clocks
only measuring order of events.  A can cause B, not vie versa
lamport diagrams/ spacetime daigrams

network models
synhcrnous network is one where exists an n such no message takes longer than n 
asynchrnous - one where the is no n such that no message takes longer than n units
"partially synchrnous" n exists but you don't know what it is

happens before - on same process. if a is send,, and b is receive, then a is before c, trasntivity
concurrent - not ordered

state - 


mate soos talking about adding mpi
z3 had mpi but was disabled.
armin biere talking about pthreads - pligenling uses pthreads
https://twitter.com/SoosMate/status/1375935222907305988?s=20
https://www.researchgate.net/publication/221403132_A_Concurrent_Portfolio_Approach_to_SMT_Solving