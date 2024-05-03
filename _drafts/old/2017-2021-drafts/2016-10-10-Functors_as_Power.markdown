---
author: philzook58
comments: true
date: 2016-10-10 22:11:51+00:00
layout: post
link: https://www.philipzucker.com/?p=525
published: false
slug: Functors as Power
title: Functors as Power
wordpress_id: 525
---

The trouble with being handed a fully functioning Haskell is that you cannot appreciate the gradations of power you can hand a language.

If one were to be building a language from scratch, you have to give the language fundamental powers. Primitive operations that can be combined (this combination is also a fundamental power (pairing, function creation, others)) to create more complicated things. These powers don't necessarily have to be orthogonal. From a reality of computing perspective, it makes sense to make your fundamental powers things hardcoded into the common architecture of cpus. 32, 64 bit integer ops, floats, bit operations, maybe memory shuffling.

From the 1000foot view it makes sense to define your starting point in terms of things that are mathematically elegant, a small tight orthogonal set of axiomatic powers that draw inspiration from some big incomprehensible math book. Then the responsibility of mapping this small set into hardware can be done fairly dumbly if you don't care about performance, or someone can spend a great deal of time ( SPJ?) making the mapping really nice.

Haskell has polymorphic types. They support defining types with type variables and self referential definitions. This is pretty crazy, and useful.But complicated. It feels like you have lambda abstraction aka function definition sort of at the type level, which is cool.

What's the minimum viable thing that feels like type variables?

Reading Harper's Practical Foundations for Programming languages, I get the feeling that surprisingly the simplest possible thing is to bake Functor definition and Map as fundamental powers in your language. Functor is sort of a 1 type variable type. map is the dynamical evaluation power that your need to use functors in any interesting way.

Functors are supposed to be mappings between categories, which on our case means mappings between types. They are functions that given a type produce a new type.

Since I don't have namespaces they will be anonymous Functors like anonymous functions.

Map is going to follow the roadmap of the functor type handed to it to know how to traverse inside and apply the function in the appropriate places.

We aren't going to need special constructors for functors since they will be constructed of the types already at hand.


