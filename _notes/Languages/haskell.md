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
- [Parametericity](#parametericity)
- [Algebra of Programming](#algebra-of-programming)
- [Category Theory](#category-theory)
- [STG and low level](#stg-and-low-level)
  - [Unboxed types](#unboxed-types)
- [Laziness](#laziness)
  - [Knot Tying](#knot-tying)
- [Extensions](#extensions)
- [Typelevel Programming](#typelevel-programming)
- [Typeclasses](#typeclasses)
- [Pipes etc](#pipes-etc)
- [Pearls](#pearls)
- [Resources](#resources)

```haskell
import qualified Data.Set as Set 

data Foo = Bar | Biz deriving Show


main :: IO ()
main = do
    print "hello world"
    print [2 * i | i <- [1.. 10] ]
    let x = 2 * pi
    print Biz
    print x
    let x = Set.fromList [1,2,3] -- Set.empty Set.singleton
    print $ Set.member 4 (Set.insert 4 x) 


```

[ghcup](https://www.haskell.org/ghcup/)

## Libraries

<https://hackage.haskell.org/packages>
<https://github.com/krispo/awesome-haskell>

containers
<https://haskell-containers.readthedocs.io/en/latest/>

<https://hackage.haskell.org/package/text> oh yeah. Is it still a thing that good strings are a package?

<https://hackage.haskell.org/package/bytestring>

<https://hackage.haskell.org/package/term-rewriting>

<https://hackage.haskell.org/package/unification-fd>

pandoc

aeson json needs

<https://hackage.haskell.org/package/attoparsec>

<https://hackage.haskell.org/package/logict>

bizarro verse
<https://hackage.haskell.org/package/kan-extensions>

criterion

mtl

vector

<https://hackage.haskell.org/package/sbv>

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

<https://www.reddit.com/r/haskell/comments/74t23t/classic_paper_review_bananas_lenses_envelopes_and/>
<https://news.ycombinator.com/item?id=24056901>
Bananases barbed wire

# Monad

<https://stackoverflow.com/questions/44965/what-is-a-monad>
<https://stackoverflow.com/questions/3870088/a-monad-is-just-a-monoid-in-the-category-of-endofunctors-whats-the-problem>

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

<https://stackoverflow.com/questions/13352205/what-are-free-monads>

## Monad Transformers

## Algebraic Effects

<http://blog.ezyang.com/2012/01/problem-set-the-codensity-transformation/>

# Lensology

<https://github.com/cohomolo-gy/optics-resources>

# Parametericity

Free theorems
Jaseklioff and higher kinded versions of parametrcity
<https://www.well-typed.com/blog/2015/05/parametricity/>
<https://www.well-typed.com/blog/2015/08/parametricity-part2/>

# Algebra of Programming

Algerba of programming book
Backhouse

Point free

Bird and Gibbons
Algorithm Design with Haskell

<https://en.wikipedia.org/wiki/Bird%E2%80%93Meertens_formalism>

<https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/squiggol-history.pdf>

Mathematics of program construction

[program desgin by calculation](https://www4.di.uminho.pt/~jno/ps/pdbc.pdf)

# Category Theory

Compiling to categories

# STG and low level

Low level ocaml and haskell

The STG. It's curiously like a Bohm mararducci or finally tagless. Constructors are function points. I mean. They're both called tagless.
<https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/compiler/generated-code>
push-enter vs eval-apply
<https://github.com/lexi-lambda/ghc-proposals/blob/delimited-continuation-primops/proposals/0000-delimited-continuation-primops.md> continuation primop
<https://medium.com/superstringtheory/haskell-compilation-pipeline-and-stg-language-7fe5bb4ed2de>
<http://www.scs.stanford.edu/11au-cs240h/notes/ghc-slides.html#(1)> crazy slides on the full stack
<https://hackage.haskell.org/package/stgi> stg interpeter. but also a good read
--ddump-ds
--ddump-stg

<https://haskell.foundation/hs-opt-handbook.github.io/contents.html> Optimization handbook
<https://book.realworldhaskell.org/read/profiling-and-optimization.html>

`+RTS` flags. There is a runtime you know.

`Debug.trace`

<https://well-typed.com/blog/2021/01/first-look-at-hi-profiling-mode/> info table profiling. You can know what code line allocated data

<https://langdev.stackexchange.com/questions/1823/what-is-the-relationship-between-stg-and-rvsdg>

<https://www.well-typed.com/blog/2020/04/dwarf-2/> dwarf and ghc

## Unboxed types

kinds are calling conventions
levity polymorphism

# Laziness

<https://en.wikipedia.org/wiki/Strictness_analysis>

[Alexis King on laziness](https://www.youtube.com/watch?v=fSqE-HSh_NU&ab_channel=Tweag)

We can ssume the result of a function is demanded.
If you return a structure, the arguments aren't necessarily demanded
bang patterns

[why laziness thread](https://www.reddit.com/r/haskell/comments/5xge0v/today_i_used_laziness_for/)
`take 10 . sort`
where clauses only make sense because `let` kind of float / are unordered
[pure memoization](https://stackoverflow.com/questions/3208258/memoization-in-haskell/3209189#3209189) <https://github.com/conal/MemoTrie> Define toplevel stream of answers, memo function just indexes ito ths toplevel stream. However, this is linear time lookup. So MemoTrie

circular programming

[why is lazy evaluation useful](https://stackoverflow.com/questions/265392/why-is-lazy-evaluation-useful/265548#265548)

## Knot Tying

# Extensions

<https://github.com/i-am-tom/haskell-exercises>

higher rank types
liquid haskell

gadts
datakinds

backpack

impredicative types
a quicklook

# Typelevel Programming

[higher order typelevel programming](https://www.microsoft.com/en-us/research/uploads/prod/2019/03/ho-haskell-5c8bb4918a4de.pdf) Did these matchable arrows make it in

# Typeclasses

# Pipes etc

# Pearls

<https://github.com/cohomolo-gy/haskell-resources> emily pillmore's list of papers

Generalizing generalized tries

Fun with semirings

Power serious

parser combinators

impossible functional programs

```haskell
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq


main = print "hello"

-- Trie a b 
data Trie a = All -- Hmm. Put a result here? 
  -- | None  -- None is Proj (empty)
  | Skip (Trie a)  -- Skip Int (Trie a) compressed skip
  | Proj (Map.Map a (Trie a)) -- Proj Int Map.Map 
   -- | None (Trie a) ???
  deriving (Eq, Ord)

{-
data Trie { [Int]} skip list factored out.
-}

{-
Wel typed form

data Trie a b = All b | Proj (Map a b)

type = Trie Int (Trie Char ())

-}

{-
instance Functor Trie where
  fmap f All = All
  fmap f (Skip x) = Skip (fmap f x)
  fmap f (Proj m) = Proj (fmap f m)
-}

join :: Ord a => Trie a -> Trie a -> Trie a
join All x = x
join x All = x
join (Skip x) (Skip y) = (Skip (join x y))
join (Proj x) (Proj y) = (Proj (Map.intersectionWith join x y))
join (Skip x) (Proj y) = Proj $ fmap (\ y -> join x y) y
join (Proj x) (Skip y) = Proj $ fmap (\ x -> join x y) x

full = All

-- insert

{-
union :: Ord a => Trie a -> Trie a -> Trie a
union All x = All
union x All = All
union (Skip x) (Skip y) = (Skip (union x y))
union (Proj x) (Proj y) = (Proj (Map.unionWith union x y))
union (Skip x) (Proj y) = ? -- hmm. maybe there's nothing
union (Proj x) (Skip y) = ?
-}

singleton :: [Maybe a]  -> Trie a
singleton [] = All
singleton (Nothing:xs) = Skip (singleton xs)
singleton ((Just x) : xs) = Proj (Map.singleton x (singleton xs))

lookup k (Skip m) = m
lookup k All = All
lookup k (Proj m) = Map.lookup k m

{-
singleton' :: [Either a Int] -> Trie a
singleton' [] = All
singleton' (Left x : xs) = Proj (Map.singleton x (singleton' xs))
singleton' (Right n : xs) = Proj (Map.singleton x (singleton' xs))
-}
-- ixy :: [(Int,a)] -> [Maybe a] 
-- ixy :: [a] -> [Int] -> [Maybe a]
{-
trie :: [[a]] -> [Int] -> Trie a
trie ls ixs = 
  foldl ls


shift?

map :: (Trie a -> Trie a) -> Trie a  -- map?

collapse :: Trie a -> Trie a
collapse All = All
collapse (Skip m) = m
collapse (Proj m) = Map.mapWithKey (\k m' -> lookup k m') 

swap :: Trie a -> Trie a
swap All = All
swap (Skip (Proj m)) = Proj (map (\k -> Skip k) m)
swap t@(Skip (Skip m)) = t
swap (Proj m) = 

Map.lookup  


So... it's partial maps over lists of stuff.
They're kind of more like ZDDs

fresh :: State Int (Trie a)

rel1 :: Set a -> Int -> Trie a
rel1 s 0 = 

rel2 :: Set (a,a) -> Int -> Int -> Trie a
rel2 s i j | i == j    = rel1 (filter (==)  s)
           | i < j     = 
           | otherwise = 
rel3 :: Set (a,a,a) -> Int -> Int -> Int -> Trie a
-}

```

# Resources

[native delim contby alexis king](https://twitter.com/lexi_lambda/status/1511315589020753929?s=20&t=-ertSPtY87GogVCFq4f-Rw)
[recursion schemes and comonads - Tielen](https://twitter.com/luctielen/status/1516719551131574274?s=20&t=7564nBvc82Jdkz_E3ccZbA)

<https://arxiv.org/pdf/2210.04729.pdf> The Foil: Capture-Avoiding Substitution With No Sharp Edges

secrets of the ghc inliner <https://www.microsoft.com/en-us/research/wp-content/uploads/2002/07/inline.pdf>

[Haskell Wiki book](https://en.wikibooks.org/wiki/Haskell)

[Bartsoz](https://bartoszmilewski.com/)

[Conal Elliott](http://conal.net/)

- Compiling to categories
- Generalized convolution and efficient language recognition
- The simple essence of automatic differentiation
- Generic parallel functional programming

[Gonzalez](https://www.haskellforall.com/)

[Brent Yorgey](http://ozark.hendrix.edu/~yorgey/)
<https://byorgey.wordpress.com/2023/07/13/compiling-to-intrinsically-typed-combinators/>
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

Joachim Breitner - <https://www.joachim-breitner.de/publications/rec-def-pearl.pdf> more fixpoints

Matthew Pickering <https://scholar.google.co.uk/citations?hl=en&user=nRJGAIYAAAAJ>
Emily Pillmore
Nicholas Wu <https://scholar.google.co.uk/citations?user=0E8zPucAAAAJ&hl=en>
Jeremy Gibbons
Schrijvers
Andres Loh
Simon Peyton Jones
Wouter Swierstra
richard eisenberg
stephanie weirich

observable equality

[comonad reader](http://comonad.com/reader/)

haskell symposium

production haskell
effective haskell
learn you a haskell for great good
<https://book.realworldhaskell.org/read/>

Diehl - what I wish I had known learning haskell

Algebraic graphs

Fun with semiring

<https://news.ycombinator.com/item?id=37391161> physics and functional programming

[evolution of haskell programmer](https://willamette.edu/~fruehr/haskell/evolution.html)

Go through old notes

<https://www.amazon.com/Introduction-to-ComputationHaskell_-Logic-and-Automata-Undergraduate-Topics-in-Computer-Science/dp/3030769070> haskell and automata

Compaines:

- tweag
- well-typed
- serokell

[Top stack exchange questions by vote](https://stackoverflow.com/questions/tagged/haskell?tab=Votes)
