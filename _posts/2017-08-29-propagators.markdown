---
author: philzook58
comments: true
date: 2017-08-29 16:42:32+00:00
layout: post
link: https://www.philipzucker.com/propagators/
slug: propagators
title: Propagators
wordpress_id: 842
---

When I first heard about Prolog, and that it's "functions" are reversible (they are really more like relations) my first thought on how I would build such a thing was wrong. Let's say you wanted plus(x,y,z). I thought maybe you'd write three functions, one for each of the possible outputs you'd like. so x+y -> z,  x-z -> y, and y-z->x. Then it's not so hard to imagine something like wiring up the graph of connections between relations and figuring out an ordering of computation that gives you the query you want. You could make such a thing non-deterministic by returning a list of possible answers rather than a single answer if that is the case like square(x,y) (square root has plus and minus answer y-> [+sqrt(y),-sqrt(y)]).

Prolog actually uses a backtracking search mechanism though and doesn't require you to write a function 3 times (although maybe under the hood primitive addition relations might have something like this for efficiency?) which makes the thing appear all the more magical at the programmer level.

But I think that first idea is somewhat related to something called a propagator.



https://www.youtube.com/watch?v=JXOOO9MLvhs

Ed Kmett is a god. He is also horrendously opaque unless maybe you have some serious mathematical chops. The propagators are a unifying paradigm for some very disparate sounding things. The Introduction to Lattices book by Davey and Priestly he mentions is actually a fairly pleasant read. The reference about how orders are involved in programming languages that comes to mind is https://en.wikibooks.org/wiki/Haskell/Denotational_semantics. The laziness of Haskell makes a richer set of possibilities than just the result of a function is terminating or not. If you don't look inside a data type, it may not matter that that piece involved a non-terminating computation. So it turns out you can define an ordering relation between data that have non-termination in different slots. the Haskell function fix, which is sort of a nasty (or useful) recursive higher order function is called so because it is related to taking the fixed point of a function from this order theory perspective.

It is very interesting that this analogy may allows you to apply the tricks of SAT solvers to speed up parallelism and stuff. As an example, I think the idea is that a function requires previous values that are it's inputs to be computed before it can fire. So you have this mess of functions waiting to fire and every time a new answer gets completed, maybe you have to search through the mess for the next guy that is ready. But the two watched literal technique from SAT solvers is a nice way of doing this. It really reduces the number of functions from the blob you need to check by keeping tabs on only a much smaller set per intermediate result (you'd keep like a hash or list of all possible functions to check if ready to fire off after an intermediate result comes in). The two watched literal technique doesn't keep ALL the possibly firing functions in the list. Per function, they only are put into two possibility lists. And when one of those intermediate results comes in, you pop the function out of that list and put it into one of the other lists of something else it needs that hasn't come in yet. If you can't find another list to put it in, it's ready to fire off itself. Each function may end up getting inspected much less than the number of variables it has depending on the order intermediates come in rather than once per variable as you would in the naive approach.

https://www.youtube.com/watch?v=acZkF6Q2XKs

https://www.youtube.com/watch?v=DyPzPeOPgUE

http://composition.al/ This is the blog of Lindsey Kuper, who did that PhD work on LVars he mentions.

http://composition.al/blog/2013/09/22/some-example-mvar-ivar-and-lvar-programs-in-haskell/

The Bartosz Milewski himself talking about MVars (Last 2 videos in playlist)

https://youtu.be/Y5UiylhFzhI?list=PLbgaMIhjbmEm_51-HWv9BQUXcmHYtl4sw

MVars block on write if full and on read if empty. So they are useful for synchronization.

IVars can only be written to once and block on read until full. They are promises

CRDTs - https://en.wikipedia.org/wiki/Conflict-free_replicated_data_type

Propagators are mentioned here

http://choco-solver.readthedocs.io/en/latest/2_modelling.html#constraints

[https://github.com/ekmett/propagators](https://github.com/ekmett/propagators)

https://www.youtube.com/watch?v=O3tVctB_VSU&t;=467s

[http://web.mit.edu/~axch/www/art.pdf](http://web.mit.edu/~axch/www/art.pdf)


