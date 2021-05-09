---
author: philzook58
comments: true
date: 2020-11-20 19:07:10+00:00
layout: post
link: https://www.philipzucker.com/?p=3009
published: false
slug: Crypto, Protocols, Relational Specs, Concurrency
title: Crypto, Protocols, Relational Specs, Concurrency
wordpress_id: 3009
---

Concurrency
Mutex
Lock
Concurrent hash table https://en.wikipedia.org/wiki/Concurrent_hash_table
barriers
 
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


## Crypto Protocol Verification

  * https://www.ccs.neu.edu/home/riccardo/courses/csg399-sp06/
  * model checking. http://seclab.stanford.edu/pcl/mc/mc.html
  * CSP - communicating sequential logic
  * pi calculus. spi calculus https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/ic99spi.pdf
  * BAN logic https://en.wikipedia.org/wiki/Burrows%E2%80%93Abadi%E2%80%93Needham_logic
  * protocol logic  https://en.wikipedia.org/wiki/Protocol_composition_logic
  * protocol verification
  * https://www.cl.cam.ac.uk/~lp15/papers/Auth/lics.pdf paulson 
  * https://www.easycrypt.info/trac/ easycrypt
  * http://certicrypt.gforge.inria.fr/ certicrypt
  * infromation flow
  * noninterference. Low and high security information https://unsat.cs.washington.edu/papers/sigurbjarnarson-nickel.pdf
  * dolev yao model
  * proverif
  * spin
  * isabelle book 
  * https://www.cl.cam.ac.uk/~lp15/papers/Auth/
  * https://www.dmi.unict.it/giamp/ giampaulo bella
  * https://crypto.stackexchange.com/questions/34304/formal-verification-in-cryptography https://crypto.stackexchange.com/questions/5834/tools-for-modelling-and-analysis-of-cryptographic-protocols?rq=1
  * http://tamarin-prover.github.io/
  * Scyther?
  * Alloy? TLA+
  * The Mike Stay Vicary paper that started this for me
  * https://www.anilada.com/courses/15251f17/www/notes/modular-arith-crypto.pdf greg notes on crypto. Not very useful
  * https://verdi.uwplse.org/ - diostributed systesm, different but related
  * https://www.cs.cornell.edu/~shmat/shmat_survey.pdf






Relational verification







  * https://www.cs.cornell.edu/fbs/publications/HyperpropertiesCSFW.pdf hyperproperties
  * https://www.cs.purdue.edu/homes/bendy/cs590-mpl/#Barthe+SecSelfComp
  * https://alastairreid.github.io/RelatedWork/notes/information-flow/





Concurrency. 







  * O'Hearn , reynolds 70 birthday https://www.sciencedirect.com/science/article/pii/S030439750600925X
  * book of semaphores https://greenteapress.com/wp/semaphores/
  * https://danluu.com/programming-books/
  * Andrews - concurrent programming book - interesting that is starts from hoare logic. This might be a great book
  * https://www.cs.cmu.edu/~brookes/papers/seplogicrevisedfinal.pdf Brookes
  * Brinch Per Hansen - concurrent
  * Pacheco - Intro to parallel programming
  * operating systems - tenenbaum
  * principles concurrent - Ben-Ari
  * Owicki-Gries, Ashcroft. Floyd is different from hoare?
  * Resource invariant
  * schneider - on concurrent programming
  * safety v livness. safety is abscence of bad. liveness is guarantee of good. Terminating is liveness. asbence of deadlock is safety
  * mutex, semaphore, monitor
  * threads, processes, coroutines.
  * https://deadlockempire.github.io/#3-simpleCounter
  * https://lamport.azurewebsites.net/pubs/lamport-verification.pdf  https://www.microsoft.com/en-us/research/uploads/prod/2018/05/book-02-08-08.pdf Specifying systems I like this lamport guy. 
  * https://github.com/cfsamson/book-green-threads-explained
  * https://pdos.csail.mit.edu/6.824/ mit dist sys course

