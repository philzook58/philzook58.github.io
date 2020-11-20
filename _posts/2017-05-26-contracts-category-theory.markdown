---
author: philzook58
comments: true
date: 2017-05-26 11:29:41+00:00
layout: post
link: https://www.philipzucker.com/contracts-category-theory/
slug: contracts-category-theory
title: Contracts and Category Theory
wordpress_id: 716
tags:
- Category Theory
- haskell
- Javascript
---

[Contracts](https://en.wikipedia.org/wiki/Design_by_contract) are both less cryptic and less impressive than a type system.

A type system somehow proves that things will never happen at compile time. You'll never get a string when you expected an int or even more powerful facts. Contracts just guarantee that at least if certain problems occur at least the program will freak out and tell you at runtime.

I had been vaguely aware of contracts which I considered to be kind of a band aid Racket thing that is their solution to type safety (besides typed racket), but I did not go into depth. And I kind of viewed the thing more as a methodology for showing loop invariants and algorithmic correctness rather than type correctness. I do not know if this is an accurate portrayal of what is in Racket and I'm pretty sure contracts do not actually originate there (Eiffel?).

Mike Stay (who you may know as the co-author of the Rosetta Stone paper [https://arxiv.org/abs/0903.0340](https://arxiv.org/abs/0903.0340))made a bunch of videos which I don't know how I didn't come across before (they're kind of old by skateboarding millennial mountain dew front end developer standards. Did Node even exist? Barely.). Javascript (well maybe after python) was my language of greatest comfort a couple years ago and I would have loved this. I absolutely loved [Bartosz Milewski's Category Theory for Programmer's ](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)series. There is a crap-ton of line noise  that kind of muddies the waters though in javascript. I wonder if it makes sense to me because I mostly already understand what he's going for from a Haskell context. He has some cool patterns here like using objects as typeclasses/interfaces.

https://www.youtube.com/playlist?list=PLwuUlC2HlHGe7vmItFmrdBLn6p0AS8ALX

[https://jscategory.wordpress.com/](https://jscategory.wordpress.com/)

The really neat thing he discusses is higher order contracts which I'd bet is a central piece of contract based programming but I had never gotten that far.

I'm still skimming over the vids, but nice job.


