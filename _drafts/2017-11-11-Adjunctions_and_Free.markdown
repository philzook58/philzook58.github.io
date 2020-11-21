---
author: philzook58
comments: true
date: 2017-11-11 01:41:29+00:00
layout: post
link: https://www.philipzucker.com/?p=920
published: false
slug: Adjunctions and Free
title: Adjunctions and Free
wordpress_id: 920
---

Adjunctions are a relation between two functors

There is an isomorphism (a invertible correspondence) between two polymorphic functions

(F a -> b) <-> (a <-> G b)

It is written

F -| G

Alternatively, you can write unit and counit functions

F G a -> a

a -> G F a

reversed turnstile. The order matches the order in the hom correspondances.

The first adjunction people talk about is F = (e,)  G = (->) e

This is (e,a)->b  is the same really as a -> (e -> b) which is true because of currying.



This post also has cool string diagrams. Adjunctions are widened lines, kind of like how strings are widened feynman diagrams?

http://www.stephendiehl.com/posts/adjunctions.html



Data Types a La Carte

http://www.cs.ru.nl/~W.Swierstra/Publications/DataTypesALaCarte.pdf

It uses recursion schemes (which use the Fix data type) plus the idea of having other combinators for things of kind * -> *.

http://reasonablypolymorphic.com/blog/better-data-types-a-la-carte

http://blog.sumtypeofway.com/

the fix data type and recursion schemes.

:+: is a combinator that takes the

the signature of an algebra is the set of possible



newtype ForgetMonad f a = ForgetMonad f a deriving Functor


