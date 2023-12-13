---
author: philzook58
comments: true
date: 2020-03-13 23:08:27+00:00
layout: post
link: https://www.philipzucker.com/?p=2709
published: false
slug: Isabelle/HOL is a strange beast
title: Isabelle/HOL is a strange beast
wordpress_id: 2709
---




I've cut my teeth in Coq and Agda and Idris, but Isabelle is different enough that it is kind of bewildering. 







All of those are dependently typed languages.








https://www.youtube.com/watch?v=cIX3WVO48RY&t=3904s









https://www.youtube.com/watch?v=Uav5jWHNghY








[https://www.isa-afp.org/](https://www.isa-afp.org/)







If you don't care about proving at all and just want to program in isabelle (and that tends to be the place you should start from) that isn't so hard. It has the backwards ass version of 'a list. These are general ML family things. 







Isabelle makes you put things in quotes.







==> is the metalevel implication I think. What does that mean







--> implication







=> function typing







Isabelle/HOL is known for having good automation. This however makes it difficult to understand what is the most primitive layer of constructs







  * rule
  * erule
  * drule
  * frule
  * assumption
  * induction






Printing stuff. There are panels to help you search in the isabelle IDE. I actually have a very difficult time understanding them and what they can see.







  * simp
  * auto
  * blast
  * fastforce
  * sledgehammer
  * arith
  * sos
  * linarith






While defining via `fun` looks very much like a pattern matching, it has some extra flavor to it. The equality it is expressing is actually a formula equality that can be thrown around. Each pattern match line can actually be named







Isar is a different syntax / mode for proving. It gives things a more human readable style.







The old tutorial is still pretty useful in so far as it is thorough







Concrete Semantics







HOL-Light tutorial and the Harrison Book. It's pretty different but still it can help acclimate you to the universe.









