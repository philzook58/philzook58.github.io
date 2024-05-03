---
author: philzook58
comments: true
date: 2017-12-14 14:03:47+00:00
layout: post
link: https://www.philipzucker.com/?p=947
published: false
slug: How does Aff work
title: How does Aff work
wordpress_id: 947
---

One of the initially alarming and offputting things about purescript is the Eff monad. The IO monad from haskell is bad enough (I think I've heard the developers are considering just adding an IO monad)

On top of that though

One of the really cool things about purescript is how natural the foreign function interface (FFI) is into javascript. It is pretty important, since the javascript ecosystem is so huge and the purescript ecosystem is a bit smaller. It is also interesting because almost everyone can read Javascript. Javascript isn't scary until you know a lot. To see the equivalent goo in Haskell, you'd have to dip into C. By the low level nature of C, it isn't going to be as easy.

Check out this

https://github.com/slamdata/purescript-aff/blob/v4.0.1/src/Control/Monad/Aff.js

This is the runtime implementation of the Aff monad. It has a scheduler and a pool of resources



When you think of how you might implement the equivalent of a new data type from Haskell or Purescript in another language like python or C or whatever, The first inclination I think is to add a Tag corresponding to the individual constructors. Then pattern matching and case statements can be implemented as a switch-scase style expression checking the tag and running the corresponding code.

The Purescript FFI implements functions as manually curried javascript functions, arrays as arrays, numbers as numbers. The more curious thing is the implementation of more complex data types.

(Question for self: How does purescript hand off typeclass info? Is there a reflection library? https://github.com/paf31/purescript-reflection Of course there is. What about constraints? It appears not. That does require ConstraintKinds)

Purescript kinds:

https://github.com/purescript/purescript/pull/2486




