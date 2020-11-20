---
author: philzook58
comments: true
date: 2017-09-21 21:07:51+00:00
layout: post
link: https://www.philipzucker.com/cellular-automata-haskell/
slug: cellular-automata-haskell
title: Cellular Automata in Haskell
wordpress_id: 885
---

[Ben](https://github.com/ishmandoo/haskell/blob/master/cell.hs) recently tried this and I wanted to see if I could do it my way

I've seen this done (Bartosz?) before but I tried to do it without looking anything up.

The comonad is an interesting pattern to use. It automates the translation invariant nature off the cellular automata. This would also be useful for translationally invariant PDEs like the simple wave equation or others.

I used the laziness of Haskell to start with an infinite plane of zeros. Of course if you ever want to look at it, you need to pick a finite slice at the end using dtake

    
    {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
    import Control.Comonad
    import Data.Bits
    
    {-
    example usage
    This pushes forward the initial state forward by 1 time step according to rule 30
    let s1 = extend (cellRule 30) initState
    
    Comments:
    My rule is coming out right-left swapped compared to Wolfram?
    I should probably custom implement Show, since the left list is printed out of order
    -}
    
    
     -- a two sided list with focus
     --alternatively may be preferable to not use those inner lists and instead make more recursive.
     --I have implicitly assume that these lists are infinite, which is bad practice. Sorry.
    data DoubleList a = DList [a] a [a] deriving (Functor, Show)
    
    data CellValue = Alive | Dead deriving Show
    
    lshift (DList (l:ls) x rs) = DList ls l (x:rs) 
    rshift (DList ls x (r:rs)) = DList (x:ls) r rs
    
    toList (DList ls x rs) = ls ++ [x] ++ rs
    lList (DList ls _ _) = ls
    rList (DList _ _ rs) = rs
    
    -- truncates the Dlist to 2n + 1
    dtake n (DList ls x rs) = DList (take n ls) x (take n rs)
    
    --kind of ugly
    --f is a function that uses the context
    -- patches together the result out of doing it on shifted Dlists
    instance Comonad DoubleList where
      extract (DList _ x _) = x
      extend f z = DList (l:ls) (f z) (r:rs) where
        lDList = extend f (lshift z)
        ls = lList lDList
        l = extract lDList
        rDList = extend f (rshift z)
        rs = rList rDList
        r = extract rDList
    
    cellToNum Alive = 1
    cellToNum Dead  = 0
    cellNeighborToNum x y z = x' + 2 * y' + 4 * z' where
      x' = cellToNum x
      y' = cellToNum y
      z' = cellToNum z
    
    cellRule :: Int -> (DoubleList CellValue -> CellValue )
    cellRule rulenum (DList (l:ls) x (r:rs)) = if testBit rulenum y then Alive else Dead where
      y = cellNeighborToNum l x r :: Int
       
    
    
    initState = DList deads Alive deads where deads = repeat Dead
    
    
    
    





