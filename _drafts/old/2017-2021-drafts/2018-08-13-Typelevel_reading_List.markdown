---
author: philzook58
comments: true
date: 2018-08-13 00:43:57+00:00
layout: post
link: https://www.philipzucker.com/?p=1192
published: false
slug: Typelevel reading List
title: Typelevel reading List
wordpress_id: 1192
---

There is some more interesting work on typelevel lambda calculus

A Typelevel programming Reading List

Basics: Justin Le and that one. http://www.parsonsmatt.org/2017/04/26/basic_type_level_programming_in_haskell.html



[http://h2.jaguarpaw.co.uk/posts/hkd-pattern-type-level-ski/](http://h2.jaguarpaw.co.uk/posts/hkd-pattern-type-level-ski/)

https://www.reddit.com/r/haskell/comments/950zn0/haskell_with_only_one_type_family_and_firstclass/

Here Oleg discusses how to reflect a value level tern to describe a typelevel lambda term.

[https://mail.haskell.org/pipermail/haskell-cafe/2011-February/089184.html](https://mail.haskell.org/pipermail/haskell-cafe/2011-February/089184.html)

Where the hell is the record of all of Oleg's mailing list posts.

[http://okmij.org/ftp/Haskell/TypeClass.html#Haskell](http://okmij.org/ftp/Haskell/TypeClass.html#Haskell)1

[http://blog.poisson.chat/posts/2018-08-06-one-type-family.html](http://blog.poisson.chat/posts/2018-08-06-one-type-family.html)



In particular, an interesting type disequality definition using a closed type family.

He uses that to stop something when it no longer matches something. closed type families do give you extra power that feels like an overlapping instance

[http://blog.poisson.chat/posts/2018-06-06-hlists-dependent-haskell.html](http://blog.poisson.chat/posts/2018-06-06-hlists-dependent-haskell.html)



The Apply typeclass is in the core of HList

[http://hackage.haskell.org/package/HList](http://hackage.haskell.org/package/HList)

http://hackage.haskell.org/package/HList-0.5.0.0/docs/Data-HList-FakePrelude.html "Polymorphic functions are not first class in haskell"

Clearly HList holds a lot of pertinent technology



Everyone is mentioning Defunctionalization as a touch stone. To some degree, this may be related to my encapsulation of morphism technique

https://typesandkinds.wordpress.com/2013/04/01/defunctionalization-for-the-win/



https://reasonablypolymorphic.com/blog/higher-kinded-data/

Things to try:

I could make the implied type entirely driven by b. I suspect this will not compile without complaint. However, if it does, it may remove the necessity of the V notation.

I had been thinking of requiring b be Generic, but now I'm less sure.

Memoization of seen values / labelling of internal nodes.

Need a keyed HList. = [(key,val)]

http://hackage.haskell.org/package/type-level-sets

And an associated paper

http://www.cl.cam.ac.uk/~dao29/publ/haskell14-effects.pdf

data Keyed key val = Keyed val

dup at lowest common ancestor and carry through?



Backtracking search in typeclass? Pertinence of the Oleg post on backtracking here?

http://okmij.org/ftp/Haskell/TypeClass.html#Haskell1



data FreeCat a b where

Id :: FreeCat a a

Comp ::

Par ::

instance Show FreeCat a b where

show Id = "Id"

show Comp x y = ""



instance graphCat

gaphviz is a simple language

http://www.michaelburge.us/2017/09/01/how-to-use-graphviz-in-haskell.html

can just hand it a list of vertices and edges it seems like, without figuring out fgl

    
    <code data-lang="haskell" class="language-haskell">  <span class="kr">let</span> <span class="n">dotGraph</span> <span class="o">=</span> <span class="kt">G</span><span class="o">.</span><span class="n">graphElemsToDot</span> <span class="n">fileGraphParams</span> <span class="n">vs</span> <span class="n">es</span> <span class="o">::</span> <span class="kt">G</span><span class="o">.</span><span class="kt">DotGraph</span> <span class="kt">FilePath</span></code>






JESUS CHRIST

http://okmij.org/ftp/Haskell/types.html

checkout de-typechecking. That is the ESSENCE of what we're doing here. OF COURSE OLEG DID IT.

Tracing back HList, it seems like the most modern type equality predicate is

http://okmij.org/ftp/Haskell/de-typechecker.lhs

Wait AND A POINTFREE TRANSLATOR?!?! GODDAMNIT.

he used overlapping instances to achieve a type equality predicate that apparently works for polymorphized types.

He does not do tuples, although that is a relatively small change.

HList is a beast. It does have tagged type level lists with lookup, which is what I thought I'd need.

I don't need to detect polymorphism persay, I need to lookup things in



If we destruct the

So Incoherent Instances gets us what we need. We can detect, in a sense, something not obviously being a tuple.

    
    {-# LANGUAGE DataKinds, AllowAmbiguousTypes, TypeFamilies, TypeOperators, MultiParamTypeClasses, FunctionalDependencies, PolyKinds, FlexibleInstances, UndecidableInstances #-}
    
    module Main where
    
    import Lib
    import Data.HList
    import Data.Proxy 
    import Data.Type.Equality
    main :: IO ()
    main = someFunc
    
    
    tup2hlist :: (a,b) -> HList '[a, b]
    tup2hlist (x,y) = HCons x (HCons y HNil)
    
    -- I feel like this won't work. This is the exxesnce of Oleg's IsFunction
    -- As far as I know, I need to use overlapping insatnces
    type family IsTup a where
    	IsTup (a,b) = 'True
    	IsTup _ = 'False
    --class IsTup'' a b | a -> b
    --instance ((a == (b,c)) ~ flag) => IsTup'' a flag 
    
    class Test a flag | a -> flag where
    	test :: a -> Proxy flag
    instance (IsTup' a flag) => Test (a -> a) flag where
    	test _ = Proxy
    
    class UnifyIf b a a'
    instance (a ~ b) => UnifyIf 'True a b
    instance UnifyIf 'False a b
    
    class IsTup' a b | a -> b
    instance {-# INCOHERENT #-} (c ~ 'True) => IsTup' (a,b) c
    instance {-# INCOHERENT #-} (b ~ 'False) => IsTup' a b
    
    -- HOccurs e h  => HasConstr 'True 
    
    
    
    {-
    
    -- To avoid problems, I should unify the things with concrete labels anyway. Just so I don't need more incoherent instances
    type family InRecord where -- InHList really.
    	InRecord l ('HCons l x) = 'True
    	InRecord l ('HCons _ x) =  'False
    	InRecord _ 'HNil = 'False
    
    instance (a ~ (b,c)) =>  Build a 'True
    
    
    instance (n ~ a) => Build a 'False where
    	build _ = emptyRecord 
     -- 'False (is not tup) -- Introduces new b, c, which is not a problem for the leaves
    -- I think the type check is strict, so this will not work
    
    -- we need a BFS? We need a complete search for 
    
    -- We can't detect polymorphism
    -- But I think we can detect polymorphic equality (a == b) -> 'False, a==a -> 'True
    -- So instead of labelling, we can do a search, but with a very particular ordering to avoid blowup.
    (a ': as) (b ': bs)
    
    
    -- Fully polymorphic either is also ok..., Either a b -> a -- Actually is not inhabitted at all
    -- either (a -> c) (b->c) (Either a b)
    -- a -> Either a b -- this is Left. Either a a -> a -- Is unique. Ingnore Left / Right. drop 
    -- So we could in principal deconsctruct Generic types
    -- 
    
    
    
    -- No because b may not be in a ultimately.
    instance If (a == b)  , '[]  => Find a b 
    
    
    instance Build (a,b) where
    	build loc =  -- Biggest chunks to smallest
    	                (Label :: Label a) .=. (fst . loc)  .*.  
    	                (Label :: Label b) .=. (snd . loc)  .*. -- append actually
    	                build (fst . loc)  .*.  
    	                build (snd . loc)
    
    -- Maybe type level records doesn't help much
    
    instance (a ~ (b,c))=> Find a 'False -- a is not in record
    
    instance Find a 'True
    	find rec = hLookUpByLabel a rec
    	      --  -> Record '[Tagged a (o->a), Tagged b Char]
    
    
    
    -}
    
    examplelist = HCons "ehllo" (HCons True (HCons False HNil))
    
    -- Type signature directs which one to grab
    -- does not compile if more than one
    ex2 :: String
    ex2 = hOccurs examplelist
    
    ex3 :: [Bool]
    ex3 = hOccursMany examplelist
    
    x = Label :: Label "x"
    y = Label :: Label "y"
    z = Label :: Label "z"
    
    
    ex4 = x .=. "v1" .*. y .=. '2' .*. emptyRecord
    
    
    ex5 = hLookupByLabel x ex4
    
    
    
    -- Whoa. HCurry looks awesome. Reflecting the Arity of the function
    -- 
    ex6 :: HList '[a,b] -> a
    ex6 = hUncurry const
    
    ex7 = hUncurry' (Proxy :: Proxy (HSucc (HSucc HZero))) const
    
    
    



