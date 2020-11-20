---
author: philzook58
comments: true
date: 2018-07-28 21:52:35+00:00
layout: post
link: https://www.philipzucker.com/shit-compiling-categories-using-type-level-programming-haskell/
slug: shit-compiling-categories-using-type-level-programming-haskell
title: Shit Compiling to Categories using Type level Programming in Haskell
wordpress_id: 1174
tags:
- compiling to categories
- haskell
- typelevel programming
---

So I've  been trying to try and approximate Conal Elliott's [compiling to categories ](http://conal.net/papers/compiling-to-categories/)in bog standard Haskell and I think I've got an interesting chunk.

His approach in using a GHC plugin is better for a couple reasons. One really important thing is that he gets to piggy back on GHC optimizations for the lambdas. I have only implemented a very bad evaluation strategy. Perhaps we could recognize shared subexpressions and stuff, but it is more work. I seem somewhat restricted in what I can do and sometimes type inference needs some help. Not great. However, GHC plugins definitely bring their own difficulties.

What I've got I think still has roots in my thinking from this previous [post](http://www.philipzucker.com/garbage-can-compiling-categories-inspectable-lambdas/)

There are a couple insights that power this implementation



 	
  1. A fully polymorphic tuple to tuple converter function is uniquely defined by it's type. For example, swap :: (a,b) -> (b,a), id:: a -> a, fst :: (a,b) ->a, snd::(a,b)->b are all unique functions due to the restrictions of polymorphism. Thus typelevel programming can build the implementation from the type.

 	
  2. Getting a typeclass definition to notice polymorphism is hard though. I haven't figured out how to do it, if it is even possible. We get around it by explicitly newtyping every pattern match on a polymorphic variable like so \(V x, V y) -> (y,x). Two extra characters per variable. Not too shabby.

 	
  3. You can abuse the type unification system as a substitution mechanism. Similar to HOAS, you can make a lambda interpreter at the type level that uses polymorphism as way of generating labels for variables. This is probably related to Oleg Kiselyov's type level lambda calculus, but his kind of confuses me [http://okmij.org/ftp/Computation/lambda-calc.html#haskell-type-level](http://okmij.org/ftp/Computation/lambda-calc.html#haskell-type-level)

 	
  4. You can inject a categorical literal morphism using a wrapping type to be extracted later using an apply operator and type App f a. An infix ($$) makes it feel better.



    
    class Eval e r | e -> r
    
    data App f b
    newtype V a = V a
    type Lit a = V a
    type Lam a b = a -> b -- Let's borrow arrow for Lambda
    
    instance (Eval b d, a ~ c) => Eval (App (a -> b) c) d
    instance (Eval b c) => Eval (a -> b) (a -> c) -- Evaluate inside the body or stop?
    instance Eval (Lit a) (Lit a)
    




So here is the rough structure of what the typelevel programming is doing

You can do a depth first traversal of the input tuple structure, when you hit V, unify the interior type with a Nat labelled Leaf. At the same time, you can build up the actual value of the structure so that you can apply the lambda to it and get the output which will hold a tree that has morphism literals you want.

Then inspect the output type of the lambda which now has Nat labels, and traverse the labelled tree again to find the appropriate sequence of fst and snd to extract what you need. If you run into an application App, you can pull the literal out now and continue traversing down.

At the moment I've only tested with the (->) Category, which is a bit like demonstrating a teleporter by deconstructing a guy and putting back in the same place, but I think it will work with others. We'll see. I see no reason why not.

At the moment, I'm having trouble getting GHC to not freakout unless you explicitly state what category you're working in, or explicitly state that you're polymorphic in the Category k.

Some future work thoughts: My typelevel code is complete awful spaghetti written like I'm a spastic trapped animal. It needs some pruning. I think all those uses of Proxy can be cleaned up by using TypeApplications. I need to implement some more categories. Should I conform to the [Constrained-Categories](http://hackage.haskell.org/package/constrained-categories) package? Could I use some kind of hash consing to find shared structures? Could Generic or Generic1 help us autoplace V or locate polymorphism? Maybe a little Template Haskell spice to inject V?

Here's the most relevant bits, with my WIP git repository [here](https://github.com/philzook58/shit-ccc)



    
    {-# LANGUAGE FunctionalDependencies, 
    FlexibleInstances, GADTs, DataKinds, TypeOperators, KindSignatures, PolyKinds,
    FlexibleContexts, UndecidableInstances, ScopedTypeVariables, NoImplicitPrelude #-}
    module Main where
    
    import Lib
    import GHC.TypeLits
    import Data.Proxy
    import Prelude hiding (id, fst, snd, (.))
    main :: IO ()
    main = someFunc
    
    
    -- We will use these wrappers to know when we've hit polymorphism
    
    newtype V a = V a
    
    
    
    data Z
    data S a
    
    
    data Leaf n a = Leaf
    data Node n a b = Node a b
    
    ccc' :: Top a b c k => Proxy k -> a -> k b c
    ccc' _ f = ccc f
    
    class Tag a b c d mono | a b mono -> d c where
        val :: Proxy a -> Proxy b -> Proxy mono -> a
    instance (Tag a n n'' r1 a', 
        Tag b n'' n' r2 b', (a', b') ~ q) => Tag (a, b) n n' (Node n'' r1 r2) q where
        val _ _ _ = (val (Proxy :: Proxy a) (Proxy :: Proxy n) (Proxy :: Proxy a'), val (Proxy :: Proxy b) (Proxy :: Proxy n'') (Proxy :: Proxy b'))
    instance (a ~ Leaf n a') => Tag (V a) n (S n) (Leaf n a') a' where
        val _ _ _ = V Leaf
    
    class CartesianCategory k => Top a b c k | a b -> c where
       ccc :: a -> k b c
    instance (Tag a Z n labels c,
             Build labels b c d k,
             CartesianCategory k)
        => Top (a->b) c d k where
            ccc f = build (Proxy :: Proxy labels) (Proxy :: Proxy b) res where
                    res = f (val (Proxy :: Proxy a) (Proxy :: Proxy Z) (Proxy :: Proxy c))
    
    
    fan f g = (par f g) . dup
    
    -- Once you've labelled, traverse the output type and extract those pieces
    -- and put them together
    class CartesianCategory k => Build labels b c d k | labels b -> c d where
        build :: Proxy labels -> Proxy b -> b -> k c d
    instance (Build labels b i o1 k, Build labels c i o2 k) => Build labels (b,c) i (o1,o2) k where
        build pl pbc (x,y) = fan (build pl (Proxy :: Proxy b) x) (build pl (Proxy :: Proxy c) y)
    instance (Extract labels n a b, CartesianCategory k) => Build labels (Leaf n c) a b k where
        build pl pb _ = extract pl (Proxy :: Proxy n)
    instance (Build labels c a b k, CartesianCategory k) => Build labels (App (k b d) c) a d k where
        build pl pb (App f x) = f . (build pl (Proxy :: Proxy c) x)
    
    
    class StripN a b | a -> b 
    instance (StripN a a', StripN b b') => StripN (Node n a b) (a',b')
    instance StripN (Leaf n a) a
    
    -- Builds the extractor function
    class Extract a n d r | a n -> d r where
        extract :: CartesianCategory k => Proxy a -> Proxy n -> k d r
    instance (LT n n' gt, -- which one is greater
              StripN (Node n' a b) ab,
              FstSnd gt ab r1, -- get value level rep of this
              ITE gt a b c, -- Select to go down branch
              Extract c n r1 r) -- recurse
                => Extract (Node n' a b) n ab r where
        extract _ p = (extract (Proxy :: Proxy c) p) . (fstsnd (Proxy :: Proxy gt))
    instance Extract (Leaf n a) n a a where
        extract _ _ = id
    
    
    
    
    arrccc :: (Top a b c (->)) => a -> b -> c
    arrccc = ccc' (Proxy :: Proxy (->))
    
    -- applying the category let's us imply arrow
    example6 = ccc (\(V x) -> x) 'a'
    
    
    
    --example7 :: CartesianCategory k => k _ _
    example7 = arrccc (\(V x, V y) -> x)  -- ('a','b')
    
    example8 = arrccc (\(V x, V y) -> y) --  ('a','b')
    example9 = arrccc (\(V x, V y) -> (y,x)) --  ('a','b')
    example10 = arrccc (\((V x,V z), V y) -> (y,x)) -- ((1,'b'),'c')
    swappo = arrccc $ \((V x,V z), V y) -> (x,(z,y))
    
    
    
    class FstSnd a d r | a d -> r where
        fstsnd :: CartesianCategory k => Proxy a -> k d r 
    
    instance FstSnd 'True (a,b) a where
        fstsnd _ = fst
    
    instance FstSnd 'False (a,b) b where
        fstsnd _ = snd
    
    
    
    class Fst a b | a -> b
    instance Fst (a,b) a
    
    class Snd a b | a -> b
    instance Snd (a,b) b
    
    class ITE a b c d | a b c -> d
    instance ITE 'True a b a
    instance ITE 'False a b b
    
    class GT a b c | a b -> c
    instance GT a b d => GT (S a) (S b) d
    instance GT Z (S a) 'False
    instance GT (S a) Z 'True
    instance GT Z Z 'False
    
    class LT a b c | a b -> c
    instance LT a b d => LT (S a) (S b) d
    instance LT Z (S a) 'True
    instance LT (S a) Z 'False
    instance LT Z Z 'False
    
    
    -- For external function application
    data App f a = App f a
    
    f $$ x = App f x
    
    plus :: (Int, Int) -> Int
    plus (x,y) = x + y
    plus' (x,y) = x + y
    
    inc :: Int -> Int
    inc = (+ 1)
    --example11 = ccc (\(x,y) -> App plus (x,y))
    
    example11 = arrccc (\(V x) -> App inc x) --  $ (1 :: Int)
    example12 = arrccc (\(V x,V y) -> plus $$ (x,y))
    example13 = arrccc (\(V x,V y) -> inc $$ (plus $$ (x,y)))
    example14 :: Num a => (a,a) -> a -- Without this annotation it inferred Integer? Monomorphization?
    example14 = ccc (\(V x,V y) -> plus' $$ (x,y))
    
    
    
    class CartesianCategory k where
        (.) :: k b c -> k a b -> k a c
        id :: k a a
        fst :: k (a,b) a
        snd :: k (a,b) b
        dup :: k a (a,a)
        par :: k a c -> k b d -> k (a,b) (c,d)
    
    instance CartesianCategory (->) where
        id = \x -> x
        fst (x,y) = x
        snd (x,y) = y
        dup x =(x,x)
        f . g = \x -> f (g x)
        par f g = \(x,y) -> (f x, g y)  
    
    
    
    





