---
author: philzook58
comments: true
date: 2017-11-10 21:49:26+00:00
layout: post
link: https://www.philipzucker.com/?p=912
published: false
slug: TypeLevel Programming
title: TypeLevel Programming
wordpress_id: 912
---

open up ghci

:set -XDataKinds



There is sort of a meta level haskell

The first version of what is going on is that there are types and there are values. Types are kind of like sets and values are like an element from that set. At compile time, we know what set we're using, but at runtime we know the actual element in use. We know x is a Float at compile time but we know x is 3.14 at runtime. (Now, sometimes we might conceivably be able to know x at compile time, say if 3.14 is hardcoded in the code rather than some runtime input. And the compiler may push through optimizations according to that, but that info has a different feel)

Kinds are the type of types. Often written as a *.

Values (3.14) <-> Types (Float)

Types (Float) <-> Kinds (*)

Kinds for simple types are not interesting.

Values of the same type are similar in some sense. They should ideally be interchangeable in the sense that the program will be capable of executing in a sensible fashion (that sensible fashion may include graceful failure if the value is bad) if you switch out values of the same type.

Are types of the same kind interchangeable? They are in a sense. Replacing one type of kind * with another type of kind * willy nilly doesn't make as much sense.

type family keyword gives you the ability to pattern match on type.

This is strange since in ordinary functions you do not need an extra keyword to transition from pattern matching into an argument and keeping it abstract

not True = False

not False = True

vs

id x = x

but in type computation you do need an extra keyword. Why?



Typeclasses are another thing that sort of to the side of the value-type-kind hierarchy, somewhere closer to types than values.

Typeclasses pattern match on Types in order to resolve themselves. This is a backtracking search process in the compiler. You can subvert this search process to your own ends.

TypeClass to Typeclass computation is defined in the

The implementation of the typeclass defines ways to convert from a typeclass to a value or a type (this is the funky Type f a :: * stuff you see sometimes).





You can not convert from a value to a type. DataKinds kind of automatically does this for you in the sense that it builds a duplicate structure of value-type at the type-kind level.

Types can be converted to values using Proxy.



The singletons library autogenerates definitions using analogies between the different layers.

It seems crazy though. You should be able to define once in a manner that is polymorphic to whether something is a kind, type, value or typeclass.

data MetaKind = **

data MetaType = Term | Type | Kind | TypeClass

data MetaValue = id | Float |* | Eq   -- (for example.)

data MetaTypeClass =  |

Doing this literally is just building an interpreter. Maybe you should use GADTs for this stuff.

metatype :: MetaValue ->  MetaType

metakind :: MetaType -> MetaKind




