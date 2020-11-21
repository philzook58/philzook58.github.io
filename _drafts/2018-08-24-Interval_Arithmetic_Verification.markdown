---
author: philzook58
comments: true
date: 2018-08-24 21:12:41+00:00
layout: post
link: https://www.philipzucker.com/?p=1252
published: false
slug: Interval Arithmetic Verification
title: Interval Arithmetic Verification
wordpress_id: 1252
---

-- Approach 1
-- Typelevel programming
-- ghc plugins may be quite helpful

https://hackage.haskell.org/package/ghc-typelits-natnormalise

and others

--data Ratio = Ratio Int Int

data Sign = Pos | Neg

data Ratio sign n d

type family RTimes x y where
RTimes (Ratio n1 d1) (Ratio n2 d2) = Ratio (n1 * n2) (d1 * d2)

-- Maybe don't used closed type family
type family Plus x y where
Plus (Ratio n1 d1) (Ratio n2 d2) = Ratio (n1 * d2 + n2 * d1) (d1 * d2)
Plus (Interval a1 b1) (Interval a2 b2) = Interval (Plus a1 a2) (Plus b1 b2)

-- Really need the full typeclass

class Plus a b c | a b -> c
plus :: a -> b -> c

type (...) = Interval
(a...b)

instance (e ~ a , f ~ d * b) => Plus (Interval a b) (Interval c d) (Interval e f) where
plus (Constrained x) (Constrained y) = Constrained (x + y)

-- data SOS

type family Floor

type family Ceil

type family Round

repeat @n a = a * (repeat @(n-1) a) -- type changes

type family RDiv x y where
RDiv (Ratio n1 d1) (Ratio n2 d2) = Ratio (n1 * ) (d1 * d2)

type family RRecip x where
RRecip (Ratio n d) = (Ratio d n)

data Interval a b -- = Interval c -- Hide definition

safeInterval :: (KnownRat a, KnownRat b) => Double -> Interval a b
safeInterval x | getRat @a =< x, getRat @b >= x = Just Interval x
| otherwise = Nothing

liftRat :: KnownNat a => Interval a a
liftRat = Interval (getNat @a)

type family ContainsZero a where
ContainsZero (Interval a b) = And (a < 0) (b > 0)

type family Contains a b where
Contains (Interval a b) (Interval c d) = And (a <= c) (b >= d)

-- discretize nonlinear functions into denominator chunks. Take Min of all chunks. Lookup table. Discretization noise.

{-
type family Reduce x where
Reduce (Radio n d) = GCD
-}



aproach 1.5 Agda

-- approach 2 Liquid Haskell
-- modern, fun
-- Would still use tagged type?

-- Approach 3 SBV



Canonical Problem:

Where does a box end up under 10 steps of linear dynamics. Nonlinear dynamics. Do all balls shrink, converging?

Do there exist inputs to make such a thing happen and what are they?

Discretization error.

8 bit discretized neural net + fixup.





Other universes:

Russell O'Connor coq real numbers

https://arxiv.org/abs/0805.2438

ROSCoq

www.cs.cornell.edu/~aa755/ROSCoq/Confidential.pdf

type classes for real computation

https://arxiv.org/pdf/1106.3448

Math Components

https://math-comp.github.io/mcb/
