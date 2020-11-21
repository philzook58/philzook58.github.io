---
author: philzook58
comments: true
date: 2018-02-14 13:42:25+00:00
layout: post
link: https://www.philipzucker.com/ignoramus-thinking-compiling-categories/
slug: ignoramus-thinking-compiling-categories
title: An ignoramus thinking about Compiling to Categories
wordpress_id: 982
tags:
- haskell
---

[http://conal.net/papers/compiling-to-categories/](http://conal.net/papers/compiling-to-categories/)

I haven't thoroughly read this (in fact barely at all) and yet I have some thoughts.

Conal Elliott is up to some good shit. Maybe ignore me and just checkout the links.

Simply Typed Lambda Calculus (STLC)

Hask is a category of haskell types with functions as arrows between them, but there is a lot going on in Haskell. Polymorphism for example, which is often modeled as some kind of Natural Transformation of EndoFunctors from Hask to Hask (but I don't think this covers every possible use of polymorphism. Maybe it does).

It is commonly mentioned that STLC is the more direct mapping. STLC is kind of a subset of haskell with no polymorphism or with the polymorphism stripped out (Every time you use a polymorphic function just monomorphize it. This blows up the number of functions floating around).

STLC is a Cartesian Closed Category (CCC), which means it is always possible to create pairs between any two types and functions between any two types.
```
data STLCType a = Prim a | Pair (STLCType a) (STLCType a) | Arr (STLCType a) (STLCType a)

data STLCTerm a = Lam Var STLCTerm | App STLCTerm | Var Var | Prim a

data Var = Var String STLCType
```



which maybe be extendible with a bunch of primitive operations and types (primitives might include addition, integers, bits, bit operations, etc.). It isn't clear to me where it is most elegant to put type annotations. Maybe it is best to keep them separate and compare them.

Apparently it is possible to compile this in a point free form
```
data CatTerm a = Comp STLCTerm STLCTerm | App STLCTerm STLCTerm | Prim a
```
or maybe
```
data CatTerm a = App STLCTerm STLCTerm | Prim a| Comp
```
Dealing with the labeling of variables correctly is a real pain in the ass, so this is a win from the compiler standpoint. It is a pain to manually write functions using this style.

The compiling to categories project I think is using Haskell as the language and GHC to do the parsing and some other stuff, but then grabbing Core (the GHC intermediate language) and converting it into the Category form. I don't see why you couldn't use an STLC DSL and do the same. It would be less ergonomic to the user but also much less complicated. I wonder. I've written interpreters for STLC and they are very simple.

Circuits form a CCC. Basic Prim type is a wire with a Boolean value on it. Pairs of these make a bus. Composition is just attaching wires between subunits. PrimOps might include Ands and Ors and Nands and multiplexers and such. Or maybe you want to work at the level where 32-bit integers are primitives and addition and subtraction and other arithmetic functions are primops.

The Arrow type is more questionable. Can you really do higher order functions in fixed circuitry? In principle, yes. Since every prim type is finite and enumerable, arrows are also finitely enumerable. You could use a varying lookup table for example as the incoming data. This is an exponential blowup though. Maybe you ought to be working in the category where arrows are types of functions that are compactly encodable and runnable. You don't want really stupidly massive circuits anyhow. Some kind of complexity theory restriction. For example, maybe you want all functions encodable in a tight BDD. You really need to shape of the BDD to be fixed. Maybe BDD whose width is bounded by some polynomial of the depth? If you don't need the full width, maybe you could leave sections dead. Just spitballin'

Or in many cases I assume the higher order functions will come applied at compile time, in which case you can just substitute the given circuit in to the locations it is needed or share it somehow (probably needs a clock to time multiplex its use) at the multiple locations it is needed to save space.

Also of extreme interest:

[http://conal.net/papers/generic-parallel-functional/](http://conal.net/papers/generic-parallel-functional/)

He's using this compiling to categories perspective with the intent to layout parallel circuits.

He uses Generic DataTypes with are very functory, which implies type parameters which tempts one into polymorphism. But I think again he is using polymorphism as a scheme which upon compilation gets turned into a bunch of different legit types. Maybe you'd want
```
data STLCType f a = Prim (f a) | Pair (STLCType f a) (STLCType f a) | Arr (STLCType f a) (STLCType f a)
```


You could do well to make way more lightweight operator synonyms for this lambda calculus
```
Lam String LC | App LC LC | Var String

(-->) = Lam
```
or
```
(\\) = Lam
```
and some synonyms for common variables
```
x = "x"

y = "y"
```
etc


```
($$) = App
```
to dereference
```
(**) = Var  - bind this very close. Trying to look kind of like pointer derferencing?
```
maybe also add pattern matching into the language
```
(Pat) =
```
And some kind of autocurrying
```
Curry [Var] |
```
Maybe use Vec instead of list for compile time size.

I guess this is gonna be funky and having the actual lambda syntax compile is super cool and nice. But it is also nice to have a userland haskell concept of this stuff without weird plugins. A OverloadLambda extension would be cool. I don't know how it would work. Type directed inference of which kind of lambda to use? Is that possible?



Also, could one piggyback on the haskell type system to make the well typing lighter weight a la the well-typed interpeter. Maybe using GADTs. http://docs.idris-lang.org/en/latest/tutorial/interp.html

It does seem unlikely that one could use raw lambdas in a good way


