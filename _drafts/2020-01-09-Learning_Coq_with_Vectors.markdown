---
author: philzook58
comments: true
date: 2020-01-09 02:37:14+00:00
layout: post
link: https://www.philipzucker.com/?p=2622
published: false
slug: Learning Coq with Vectors
title: Learning Coq with Vectors
wordpress_id: 2622
---




I'm a coq noob. I heartily admit it.







But I'm enjoying leveling up at them moment and seem to have reached a stage where I'm at least not completely helpless in coq.







What has changed:







  * I've become more comfortable and familiar with the simple tactics.
  * I found out about the powerful automatic tactics for numbers nia,lia,lra,nra, psatz, ring, ring_simplify, field. 
  * I understand a little bit better typeclasses
  * i understand a little bit better auto and the Hint system






I think the mathematical components library is by far the most active mathematical library in coq.







  * arrays / list. 
  * dependently typed sized lists
  * Functions indexed on a sized space
  * Maps
  * Composed bespoke data structures, V2 V1 V3. Structs as vectors
  * Tuples
  * linear maps to R






I made the mistake of trying to be too generic/polymorphic at first. I was somewhat familiar with the reasonable design space for vectors that exists in Haskell, and thought I'd just reuse my favorite. It was too much for a coq n00b. Abstractions are hard to do. In coq, if you want to be abstract, you are going to 







  * Give up the powerful automated tactics for N, Z, Q, R
  * Need to build up a hierarchy of power/typeclasses or understand the ones out there.
  * 

