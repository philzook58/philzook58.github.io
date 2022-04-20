---
layout: post
title: Haskell
---

# Monad

```haskell
return :: a -> m a
(>>=) :: m a -> (a -> m b) -> m b
```

"monoid in the category of endofunctors"

type constructors are endofunctors. A functor is 
1. a mapping ofobjects
2. a mapping of morphisms

The standard model of category theory in haskell is
1. types are objects
2. morphisms are functions

Composition is `(.)`. `id` are identity morphisms. 

Note how weird this is. We've in some sense put types and values (haskell functions are values that inhabit function types) on the same level.


Maybe maps any type `a` to the the  `Maybe a`


## Free Monads

## Recursion Schemes and F-Algebras

A different category

`f a -> a`
- objects are _haskell functions of this type_ and the type `a`. Again a bizarre (depending on your background) mixing of values and types
- morphisms are squares. Very very weird.


a -> f a

Initiality


## Unboxed types
kinds are calling conventions
levity polymorphism

# STG and low level
Low level ocaml and haskell

The STG. It's curiously like a Bohm mararducci or finally tagless. Constructors are function points. I mean. They're both called tagless.
https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/compiler/generated-code
push-enter vs eval-apply
https://github.com/lexi-lambda/ghc-proposals/blob/delimited-continuation-primops/proposals/0000-delimited-continuation-primops.md continuation primop
https://medium.com/superstringtheory/haskell-compilation-pipeline-and-stg-language-7fe5bb4ed2de
http://www.scs.stanford.edu/11au-cs240h/notes/ghc-slides.html#(1) crazy slides on the full stack
https://hackage.haskell.org/package/stgi stg interpeter. but also a good read
--ddump-ds
--ddump-stg

# Resources
[native delim contby alexis king](https://twitter.com/lexi_lambda/status/1511315589020753929?s=20&t=-ertSPtY87GogVCFq4f-Rw)
[ recursion schemes and comonads - Tielen](https://twitter.com/luctielen/status/1516719551131574274?s=20&t=7564nBvc82Jdkz_E3ccZbA)