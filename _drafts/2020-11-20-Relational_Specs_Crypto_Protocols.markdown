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

Yeah so securtity high information to low infornmation is formulated as relational execution of programs. The information is held in a "spooky" correlation of two executions. Does this give an interesting persepctive on the paramtricity theorem?

That mike stay vicary stuff

noninterference for free- bowman.

https://arxiv.org/pdf/1912.08788.pdf - binsec/rel
https://dodisturb.me/posts/2021-06-27-Typed-Programs-Dont-Leak-Data.html - imp like interpeter with securty levels.

Jif - suecrity properties in Java https://www.cs.cornell.edu/jif/

language based security https://en.wikipedia.org/wiki/Language-based_security https://www.cs.cornell.edu/andru/papers/jsac/sm-jsac03.pdf
infromation flow security
myers zdanvenic
pottier and siomething flow caml
goguen mesegauer - original nonterference paper



Haskell embedding of DCC
http://www.cse.chalmers.se/~russo/publications_files/plas2017.pdf
https://hackage.haskell.org/package/mac
http://www.cse.chalmers.se/~russo/publications_files/pearl-russo.pdf

This Russo guy is good to look at
Secure-multi execution
information flow securioty
Doin it in idris https://link.springer.com/chapter/10.1007/978-3-030-17138-4_3

An embedding of tags into rust
https://willcrichton.net/notes/type-level-programming/



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

