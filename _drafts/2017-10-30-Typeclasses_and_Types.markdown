---
author: philzook58
comments: true
date: 2017-10-30 15:53:08+00:00
layout: post
link: https://www.philipzucker.com/?p=907
published: false
slug: Typeclasses and Types
title: Typeclasses and Types
wordpress_id: 907
---

Propositions are types is a slogan that reflects the fact that typechecking a program and formally checking the proof of a logical theorem are the same operation.

Typeclasses are naively a way to give powers to types that are interchangeable. The power to be compared or added or all sorts of other things. Then if you just use these powers without looking at their implementation, you can write generic programs that will work on any type that has a equality definition for example.

Writing a instance (Eq Int) is a statement that Int has the power Eq

When I tried to wrap my head around multiparameter typeclasses it becomes more clear that one must consider typeclasses as relations.



The process of figuring out which implementation to use of the typeclass given the type is a searching problem, one that mimics the same searching problem that occurs in the runtime of a prolog program. Because this program is in GHC somewhere, a clever programmer can  hack his or her way into using it.

But if both types and typeclasses are relations, what is the difference?



If one writes a simpleminded program

vadd :: Vector -> Vector -> Vector

But it isn't necessarily obvious or unique what the implementation of vector is, it may be a thing you might want to try to perform the simple operation

vadd :: (Vector a) => a -> a -> a

just pull every type into a typeclass and replace the identifier with a new type parameter.

This is so mechanical, that I wonder if it can be mechanized as a higher order function.

ConstraintKinds lets you do awesome stuff

Singleton TypeClasses seem like a natural fit for specifying that a type variable is of type Int. However, I suppose you could implement isInt for a non Int. So that is bad.

class (SInt a ) where

isInt :: a -> Int



No maybe you would use

(a ~ Int) =>

as the typeclass predictae



Since typeclasses give you access to a typelevel compile time prolog, one wonders if there might be other type mechanisms you might want compile-time access into.

I suppose typelevel access to an SMT solver is via liquid haskell at the moment.

But Liquid Haskell annotation is not first class.


