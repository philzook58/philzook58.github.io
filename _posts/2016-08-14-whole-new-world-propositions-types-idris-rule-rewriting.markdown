---
author: philzook58
comments: true
date: 2016-08-14 19:46:23+00:00
layout: post
link: https://www.philipzucker.com/whole-new-world-propositions-types-idris-rule-rewriting/
slug: whole-new-world-propositions-types-idris-rule-rewriting
title: A whole new world. Propositions as types. Idris. Rule-rewriting
wordpress_id: 488
tags:
- curry-howard
- functional
- programming
---

I've been going down a rabbit hole lately. I suppose it started with I wanted to solve the annihilation creation operator algebra (and more long term understand how to program up anyons in a elegant way) in a new way. So I rebooted up my haskell.

I was hoping (through a misunderstanding of what pattern matching and lazy evaluation achieve ) I'd somehow be able to write

    
    g(3) = 4
    f(g(x))=g(f(x))
    f(2) = 3
    
    f(g(2)) = ?


This is screwy from a functional programming perspective. I'm no guru, but I think the problem is that really you want f to take a function and return a new function on line 2 whereas you want f to take an integer and return an integer on line 3.

You can hack this together, but I feel it is not an elegant approach.



Anyhow, this problem is solvable in mathematica. Mathematica (of is it called Wolfram now? I'm a tad confused there) at its core is a rule rewriting system. This is a different flavor than a functional programming langauge, I think. All the current applicable rules float around somewhere in the enviroment. Wehn you make an = expression you add a new rule. This is similar to functional programming have all the functions floating around and you can define new functions to put into the environment. equals sign and rule replacement /.{x->y} are very very related.

However, I think there is an element of nondeterminism in the rule rewriting. It can try to apply rules and fail and the untry that rule. I think? Mathematica is pretty vague as far as I can tell on what it is trying. Functional programs I think go more one way. You apply a function but then never unapply it. There is no try; only do. You could definitely build up some kind of history system to achieve this but it feels much less intrinsic to the basic evaluation procedure. The order of applications is free to be chosen. Top down, bottom up, whatever. Some sort of procedure.

So this got me curious about how I could implement such a system in a cute way or what else I could do.

Then I came across the Strange Loop talks.

https://www.youtube.com/watch?v=IOiZatlZtGU

This one in particular intrigues me.

He mentions Session Types, a typing system for communication that is analogous in some way to linear logic. Linear logic has kind of a no copy rulewhere you use up propositions when you use them rather than being usable as much as you like. Like the no-cloning theorem in Quantum. This brought me back to take a peek at Baez's Rosetta Stone paper. Interesting and cryptic. I guess this is good for communicating. Messages get sent and then used up when received. Sounds neato. Looking at the concrete specification Scribble makes this a bit more clear. Maybe this would be a good paradigm for a quantum computing programming language? Sort of let the quantum information transfer between gates be treated as a network call. It makes sense in that you would want to run different parts of quantum algorithms on quantum and classical computers. The interface probably will be network like. Quantum-Quantum Sockets and Quantum-Classical sockets. Wait for a measurement signal on the classical side, then send a classical valued configuration signal to the gates. The gates send quantum signals to each other. The classical side also needs to setup the gate connections too.

Smart people freak out about types. I don't understand why yet. They seem important in the very roots of mathematics.  Circumventing paradoxes and such. Types allow to compiler to save you from yourself (and others), I think is the main point. But they also make you figure out. I have found Haskell's type system to be useful for sketching out what I mean by writing down data structures. It can be a useful part of the thinking process. Like writing function declarations without writing the inner code. "Oh yeah, I'll need a vectorizing function. Let's write that down but code it up later." I've also found myself yearning for this in python sometimes. Stronger typing would let me pass stuff in without whatever it is I'm passing in being implied within the code of the function itself. "Error? On what? Oh, the dict should have a 'foo' key? Huh. Whoopsy." I can and should and sometimes do put that stuff in comments, but you have to read those. Which is not guaranteed.

Also, Lambda cube? Huh.

Then I saw some more talks mentioning Coq, Agda, and Idris. Language that are related somehow. Languages that touch or are intended for theorem proving. This is a subject I've seen mentioned before and not understood what that could mean. Idris is very close variant of Haskell. This seems like a good road to understand more. Coq has a long history and a difficult reputation.

Maybe the next thing I need is to learn some basics of logic to be a better programmer.

Propositions = Types.

What does that mean?

https://en.wikipedia.org/wiki/Sequent_calculus

This stuff is very evocative of lambda calculus. How have I somehow not seen this before? I guess I just sort of glazed over when the Curry-Howard isomorphism was mentioned. Assumed that was a very high falutin thing not worth checking out.

I'm still in the middle of it all. We'll see.
