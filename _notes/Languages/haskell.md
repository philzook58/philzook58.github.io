---
layout: post
title: Haskell
---

- [Functor Games](#functor-games)
  - [Applicative](#applicative)
  - [Recursion Schemes and F-Algebras](#recursion-schemes-and-f-algebras)
- [Monad](#monad)
  - [Comonads](#comonads)
  - [Free Monads](#free-monads)
  - [Monad Transformers](#monad-transformers)
  - [Algebraic Effects](#algebraic-effects)
- [Lensology](#lensology)
- [Algebra of Programming](#algebra-of-programming)
- [Category Theory](#category-theory)
- [STG and low level](#stg-and-low-level)
  - [Unboxed types](#unboxed-types)
- [Laziness](#laziness)
- [Extensions](#extensions)
- [Typeclasses](#typeclasses)
- [Pipes etc](#pipes-etc)
- [Pearls](#pearls)
- [Resources](#resources)


```haskell
data Foo = Bar | Biz deriving Show


main :: IO ()
main = do
    print "hello world"
    print [2 * i | i <- [1.. 10] ]
    let x = 2 * pi
    print Biz
    print x


```

[ghcup](https://www.haskell.org/ghcup/)



# Functor Games

## Applicative
## Recursion Schemes and F-Algebras
`Fix`

A different category

`f a -> a`
- objects are _haskell functions of this type_ and the type `a`. Again a bizarre (depending on your background) mixing of values and types
- morphisms are squares. Very very weird.


a -> f a

Initiality

https://www.reddit.com/r/haskell/comments/74t23t/classic_paper_review_bananas_lenses_envelopes_and/
https://news.ycombinator.com/item?id=24056901
Bananases barbed wire



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


## Comonads
## Free Monads
## Monad Transformers
## Algebraic Effects


http://blog.ezyang.com/2012/01/problem-set-the-codensity-transformation/


# Lensology



# Algebra of Programming
Algerba of programming book
Backhouse

Point free

Bird and Gibbons 
Algorithm Design with Haskell

https://en.wikipedia.org/wiki/Bird%E2%80%93Meertens_formalism

https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/squiggol-history.pdf

Mathematics of program construction

[program desgin by calculation](https://www4.di.uminho.pt/~jno/ps/pdbc.pdf)
# Category Theory
Compiling to categories

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

## Unboxed types
kinds are calling conventions
levity polymorphism
# Laziness

[Alexis King on laziness](https://www.youtube.com/watch?v=fSqE-HSh_NU&ab_channel=Tweag)

# Extensions


higher rank types
liquid haskell

gadts
datakinds



backpack


# Typeclasses

# Pipes etc

# Pearls
Generalizing generalized tries

Fun with semirings

Power serious

parser combinators

impossible functional programs

# Resources
[native delim contby alexis king](https://twitter.com/lexi_lambda/status/1511315589020753929?s=20&t=-ertSPtY87GogVCFq4f-Rw)
[ recursion schemes and comonads - Tielen](https://twitter.com/luctielen/status/1516719551131574274?s=20&t=7564nBvc82Jdkz_E3ccZbA)

https://arxiv.org/pdf/2210.04729.pdf The Foil: Capture-Avoiding Substitution With No Sharp Edges

secrets of the ghc inliner https://www.microsoft.com/en-us/research/wp-content/uploads/2002/07/inline.pdf

[Haskell Wiki book](https://en.wikibooks.org/wiki/Haskell)

[Bartsoz](https://bartoszmilewski.com/)

[Conal Elliott](http://conal.net/) 
- Compiling to categories
- Generalized convolution and efficient language recognition
- The simple essence of automatic differentiation
-  Generic parallel functional programming

[Gonzalez]()

[Brent Yorgey](http://ozark.hendrix.edu/~yorgey/)
https://byorgey.wordpress.com/2023/07/13/compiling-to-intrinsically-typed-combinators/
Species

Sjoerd
Kmett

Ben Lynn
Gershom Bazerman
Alexis King

Oleg Kiselyov
Ralf Hinze
[Dan Piponi](http://blog.sigfpe.com/)

Jules Hedges - games, selection monad

[comonad reader](http://comonad.com/reader/)

haskell symposium


production haskell
effective haskell
learn you a haskell for great good


Diehl - what I wish I had known learning haskell



Algebraic graphs

Fun with semiring

https://news.ycombinator.com/item?id=37391161 phsyics and functional programming


[evolution of haskell programmer](https://willamette.edu/~fruehr/haskell/evolution.html)

Go through old notes
