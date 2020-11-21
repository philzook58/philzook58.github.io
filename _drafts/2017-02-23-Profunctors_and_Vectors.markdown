---
author: philzook58
comments: true
date: 2017-02-23 23:19:37+00:00
layout: post
link: https://www.philipzucker.com/?p=666
published: false
slug: Profunctors and Vectors
title: Profunctors and Vectors
wordpress_id: 666
---

Covariant and Contravariant are terms used in both vector math and category theory / Haskell.

You have vectors

Then you have the duals of vectors which are linear functions of vectors.

data Basis = X | Y | Z

This is a contravariant functor on the basis. Simple permutative or relabelling transformations on the basis can be easily applied

type DualVec = Basis -> Float

or rather

type DualVec a = a -> Float

It also inherits a natural addition operation from the Floats.

By placing

type Vec = DualVec -> Float

These things basically wrap a number of function calls with supplied basis elements. Again because they are functorial in Float, we inherit an addition and scalar multiplication operation. Really, it could be any Num on the right. A Monoid on the right is enough for addition but not scalar multiplication.

You can keep going up in the chain, dualizing again and again

Dual b = b -> Float



Dual (Dual a) = (a -> Float) -> Float

I feel like a dual function

dual :: (a->Float) -> Dual (a-> Float)

is unique modulo all Float -> Float functions. Which are a lot.

A Monad pattern can be used to enforce linearity. Or maybe rather an Applicative pattern is enough.

Linear operators are Profunctorial in their input and output bases.

The direct sum Bifunctor can be made using + on the output

The direct product Bifunctor can be made using * on the output

A New idea:




