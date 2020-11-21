---
author: philzook58
comments: true
date: 2016-09-08 15:23:13+00:00
layout: post
link: https://www.philipzucker.com/?p=502
published: false
slug: Dependent Types
title: Dependent Types
wordpress_id: 502
---

The first chapter of the [Homotopy Type Theory](https://homotopytypetheory.org/book/) book is surprisingly readable. I thought it would be an absolutely incomprehensible mess. Maybe I have to wait for chapter two for it to become impossible. That's not to say I'm a master of the material. Here are some thoughts as I went through it.

What are types? I'm not sure. I think informally, we usually think of types kind of like sets and  the things ("judgements") a:A of type A are like elements kind of. My understanding is that homotopy type theory is about how types are like spaces and a:A are like points in spaces.

I think the big difference between types and sets is that a "judgement" a:A does not separate into something a and something A like you could in a set. 3 is an element of the Odds, and the Reals and not of the Evens. In set theory, 3 isn't really exactly defined to belong to a particular set? It sort of has a separate existence from sets. In type theory, there is implicitly always a type when we write "a".  Writing just an "a" is being informal

The Universe U is basically Haskell *  aka kind.

So Int:U, String:U, (Int->Float):U

"A" is implicitly always A:U? But then U is always actually U:U2, and then U2 is actually U2:U3. That seems worrying. Then being formal we could never write down a completed expression. We could only transition from informality to formality in stages, never finishing. Maybe some kind of lazy typing could help. We only need the type if we ask for it. I don't know. I'm really out of my depth here.

Type theory is making a strong distinction about what is definition and what is proposition.

There is both definitionally equal and propositionally equal. The second can be false. The first has no way to even formalize the question of it being false according to the type rules.

A family of types B:A->U is a kind of function that returns types. Let's say A was int. Then an example f:B is

f(1)=Int

f(2)=String

f(3)=String-> Int

etc.

$latex \Pi_(x:A) B(x) $ is the type of a dependently typed function. Let's say we make g of this type and A is an Int.

g(1) = 3:Int

g(2) = "Hi There":String

g(3) = \str -> 32+ (length str) :String-> Int

I can see how you might want to do this stuff. I feel like untyped languages like python let you do this basically anyhow. You can choose to return whatever the hell you like. But there must be some kind of distinction

Dependently type pairs are somehow brothers of dependently type functions.

(Pairs and functions are brothers somehow anyway. Look at currying or uncurrying. Or the set construction of pairs. Functions are sets of pairs where the first element is unique)

The type of the second object in the pair depends on the value of the first guy. So the there is a family there, a function taking a value x:A to an element of U.

The recursor is the church encoding (or Mogenson-Scott encoding)?

Existential Qualifiers:

for all <=> dependent typed functions

there exists <=> dependent typed pairs

A practical question: How do you determine equality of functions? Well, if they have a finite domain it sounds plausible, you just try every element in the domain and see if they match. Also, perhaps you could determine if they are the same by definition (they refer to the same chunk of code by pointer or if the code content of the code is word for word identical). Also, if you had a function from all integers, you could easily prove that two functions are not equal by checking all integers and eventually you're going to find a counterexample. There is no general procedure to do so in some sense, because such a procedure is probably equivalent to the halting problem (No, I don't know enough to come up with the exact argument. Or maybe I'm too lazy. I dunno. I'll think about it.)








