---
author: philzook58
comments: true
date: 2017-09-12 22:10:07+00:00
layout: post
link: https://www.philipzucker.com/ordered-pairs-idris/
slug: ordered-pairs-idris
title: Ordered pairs in Idris
wordpress_id: 881
---

I implemented an ordered pair type in Idris. Took me a while.

https://github.com/idris-lang/Idris-dev/blob/master/libs/prelude/Prelude/Nat.idr

Already has an inequality type. That may have been better to use.

Exploration and guesswork was necessary. How the heck do I get a hotkey for holes in atom?

The first couple Opairs are ordinary pairs. Just exploring the syntax.

I switched out of InEq which explicitly stores the number it is talking about to better match the equality type.

The Inequality type acts something like a mix of Nat and Equality.

My head hurts and I'm dehydrated.



    
    
    data OPair1 a = SimplePair1 a a
    
    data OPair2 : Type -> Type where
      SimplePair2 : a -> a -> OPair2 a
    
    data OPair3 : Type -> Type where
      SimplePair3 : (Ord a) => a -> a -> OPair3 a
    
    data InEq : Nat -> Nat -> Type where
      Refly : (t:Nat) -> InEq t t
      Succy : InEq a b -> InEq a (S b)
    
    data InEq' : Nat -> Nat -> Type where
      Refly' : InEq' t t
      Succy' : InEq' a b -> InEq' a (S b)
    
    data InEq'' : Nat -> Nat -> Type where
      Refly'' : InEq'' Z t
      Succy'' : InEq'' a b -> InEq'' (S a) (S b)
    
    
    data OPair4 : Type where
      SPair : (t : Nat) -> (s : Nat) -> (InEq t s) -> OPair4
    
    data OPair5 : Type where
      SPair5 : (t : Nat) -> (s : Nat) -> (InEq' t s) -> OPair5
    
    -- a useful lemma
    convert4 : InEq' s t -> InEq' (S s) (S t)
    convert4 Refly' = Refly'
    convert4 (Succy' x) = Succy' (convert4 x)
    
    addpair : OPair5 -> OPair5 -> OPair5
    addpair (SPair5 s s Refly') (SPair5 k k Refly') = SPair5 (s+k) (s+k) Refly'
    addpair (SPair5 Z Z Refly') (SPair5 t b p) = (SPair5 t b p)
    addpair (SPair5 (S x) (S x) Refly') (SPair5 t b p) = addpair (SPair5 x x Refly') (SPair5 (S t) (S b) (convert4 p))
    addpair (SPair5 x (S y) (Succy' z)) (SPair5 t b p) = addpair (SPair5 x y z) (SPair5 t (S b) (Succy' p))
    --addpair (SPair5 t (S b) (Succy' x)) (SPair5 k s y) = addpair (SPair5 t b x) (SPair5 k (S s) (Succy' y))
    
    
    
    
    convert : (t : Nat) -> (s : Nat) -> InEq' t (s + t)
    convert t Z = Refly'
    convert t (S k) = Succy' (convert t k)
    
    convert2 : (s : Nat) -> InEq' 0 (plus s 0)
    convert2 s = convert Z s
    
    --convert3 : InEq' 0 (plus s 0) -> InEq' 0 s
    --convert3 p = replace ?sda ?sdf
    
    convert3 : (s : Nat) -> InEq' 0 s
    convert3 s = replace (plusZeroRightNeutral s) (convert2 s)
    
    
    incrementpair : OPair5 -> OPair5
    incrementpair (SPair5 x y z) = SPair5 (S x) (S y) (convert4 z)
    
    sortpair : (Nat,Nat) -> OPair5
    sortpair (Z, Z) = SPair5 Z Z Refly'
    sortpair (Z, y) = SPair5 Z y (convert3 y)
    sortpair (y, Z) = sortpair (Z, y)
    sortpair (S x, S y) = incrementpair (sortpair (x,y))
    --sortpair (S x, S y) = addpair (SPair5 1 1 Refly') (sortpair (x,y))
    
    
    
    --addpair (SPair5 x x Refly') (SPair5 x2 y2 p) = (SPair5 (x2+x) (y2+x) p)
    --addpair (SPair5 x (S y) (Succy' p1)) (SPair5 x2 y2 p) = addpair (SPair5 x y p1) (SPair5 x2 (S y2) (Succy' p1))
    
    {-
    natToInEq : Nat -> InEq' Z t
    natToInEq Z = Refly'
    notToIneq (S x) = Succy' (natToInEq x)
    
    maybeOPair : Nat -> Nat -> Maybe OPair5
    maybeOPair a b = if (a <= b) then Just (SPair5 a b (natToInEq (b-a)))else Nothing
    -- sortpair is a better maybepair. maybepair could be implemented
    
    -}



