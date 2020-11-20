---
author: philzook58
comments: true
date: 2018-08-13 12:10:12+00:00
layout: post
link: https://www.philipzucker.com/approximating-compiling-categories-using-typelevel-haskell-take-2/
slug: approximating-compiling-categories-using-typelevel-haskell-take-2
title: 'Approximating Compiling to Categories using Type-level Haskell: Take 2'
wordpress_id: 1197
tags:
- haskell
---

The previous episode is [here ](http://www.philipzucker.com/shit-compiling-categories-using-type-level-programming-haskell/).

Summary: I'm trying to use typelevel programming in Haskell to achieve some of the aims of Conal Elliott's [compiling to categories](http://conal.net/papers/compiling-to-categories/) [GHC plugin](https://github.com/conal/concat). The types of highly polymorphic tuple functions are enough to specify the implementation. We aren't going to be able to piggy-back off of GHC optimizations (a huge downside), but we can reify lambdas into other categories and avoid the scariness of plugins.

The current implementation github source is [here ](https://github.com/philzook58/shit-ccc)



* * *



JESUS CHRIST.

[http://okmij.org/ftp/Haskell/de-typechecker.lhs](http://okmij.org/ftp/Haskell/de-typechecker.lhs)

Of course, Oleg already did it. This is a file where he builds the implementation of a polymorphic function from the type signature. Instead of tuples, he is focusing on higher order functions with deep nesting of (->).

The trick that I was missing is in the IsFunction typeclass at the very end, which is only achievable as a Incoherent instances.

I would never have had the courage to use an Incoherent instance if I hadn't seen a higher authority do it first. It has turned out in my typelevel journey that many instances that I've been tempted to make overlapping or incoherent don't actually have to be, especially with the availability of closed type families. I think you really do need Incoherent in this application because type variables stay polymorphic forever.

To the best of my knowledge, if you need to differentiate between a tuple type (a,b) and an uninstantiated polymorphic value a' like we do when deconstructing the input type of our lambda, you need to use an Incoherent instance. Since a' could hypothetically eventually be unified to some (a,b) we should not be able to do different things for the two cases without stepping outside the usual laws of typeclass resolution.

New features of the implementation:



 	
  * The new implementation does not require the V annotation of the input like previous version by using the previously mentioned. This is super cool because now I can throw the stock Prelude.fst into toCcc.

 	
  * I changed how the categorical implementation is built, such that it short circuits with an 'id' if a large structure is needed from the input, rather than deconstructing all the way to every piece of the input. Lots of other optimizations would be nice (vital?), but it is a start.

 	
  * I also implemented a FreeCat GADT so that we can see the implementation in ghci.

 	
  * I switched from using Data.Proxy to the type annotations extensions, which is a huge readability win.

 	
  * I added a binary application operator binApp, which is useful for encapsulating categorical literals as infix operators into your lambda expressions.

 	
  * General cleanup, renaming, and refactoring into library files.


A couple typelevel tricks and comments:

You often have to make helper typeclasses, so don't be afraid to. If you want something like an if-then-else in your recursion, it is very likely you need a form of the typeclass that has slots for 'True or 'False to help you pick the instance.

If possible, you often want the form

    
    (a~Something) => MyClass 'True a


rather than

    
    Myclass 'True Something


The type inference tends to be better.

Here are some usage examples of toCcc.

    
    example6 = toCcc (\x -> x) 'a'
    
    
    example7 = toCcc @FreeCat (\(x, y) -> x)
    
    example8 = toCcc @FreeCat (\(x, y) -> y)
    example8andahalf = toCcc' (Proxy :: Proxy FreeCat) (\(x, y) -> y)
    example9 = toCcc @FreeCat (\(x, y) -> (y,x)) 
    example10 = toCcc @FreeCat (\(( x, z), y) -> (y,x))
    swappo = toCcc @FreeCat $ \((x, z), y) -> (x,(z,y))
    
    example11 = toCcc @(->) $ \(x,y) -> binApp addC x y
    example12 = toCcc @(->) $ \(x,y) -> App negateC x
    
    -- infix synonyms
    (+++) = binApp addC
    (***) = binApp mulC
    example13 = toCcc @(->) $ \(x,(y,z)) -> x +++ (y *** z)


My partially implemented version of some of Conal's category typeclasses. Should I switch over to using the constrained-categories package?

    
    {-# LANGUAGE GADTs, StandaloneDeriving, NoImplicitPrelude  #-}
    
    module Cat where
    import Control.Category
    import Prelude hiding ((.))
    
    
    class Category k => Monoidal k where
        par :: k a c -> k b d -> k (a,b) (c,d)
    
    class Monoidal k => Cartesian k where
        fst :: k (a,b) a 
        snd :: k (a,b) b 
        dup :: k a (a,a) 
    
    fan f g = (par f g) . dup
    
    data FreeCat a b where
        Comp :: FreeCat b c -> FreeCat a b -> FreeCat a c
        Id :: FreeCat a a
        Fst :: FreeCat (a,b) a
        Snd :: FreeCat (a,b) b
        Dup :: FreeCat a (a,a)
        Par :: FreeCat a b -> FreeCat c d -> FreeCat (a,c) (b,d)
    
    deriving instance Show (FreeCat a b)
    
    instance Category FreeCat where
        (.) = Comp
        id = Id
    
    instance Monoidal FreeCat where
        par = Par
    
    instance Cartesian FreeCat where
        fst = Fst
        snd = Snd
        dup = Dup
    
    instance Monoidal (->) where
        par f g = \(x,y) -> (f x, g y)  
    
    instance Cartesian (->) where
        fst (x,y) = x
        snd (x,y) = y
        dup x = (x,x)
    
    class NumCat k where
        mulC :: Num a => k (a,a) a
        negateC :: Num a => k a a
        addC :: Num a => k (a,a) a
    
    instance NumCat (->) where
        mulC = uncurry (*)
        negateC = negate
        addC = uncurry (+)
    
    




The actual implementation of toCcc

    
    {-# LANGUAGE DataKinds, 
        AllowAmbiguousTypes, 
        TypeFamilies, 
        TypeOperators, 
        MultiParamTypeClasses, 
        FunctionalDependencies, 
        PolyKinds, 
        FlexibleInstances, 
        UndecidableInstances,
        TypeApplications,
        NoImplicitPrelude,
        ScopedTypeVariables #-}
    module CCC (
          CCC
        , App (App)
        , binApp
        , toCcc'
        , toCcc ) where
    
    import Cat
    import Data.Proxy 
    import Data.Type.Equality (type (==))
    import Prelude (Bool(..))
    import Control.Category
    
    
    -- The unfortunate Incoherent instances I need to force polymorphic values
    class IsTup a b | a -> b
    instance {-# INCOHERENT #-} (c ~ 'True) => IsTup (a,b) c
    instance {-# INCOHERENT #-} (b ~ 'False) => IsTup a b
    
    data Leaf n = Leaf
    
    
    data Z
    data S a
    
    
    data App f a = App f a
    
    
    f $$ x = App f x
    binApp f a b = App f (a,b)
    
    class Cartesian k => CCC k a a' b' | a a' -> b' where
       toCcc :: a -> k a' b'
    instance (Tag a,
             Build k a b a' b',
             Cartesian k)
        => CCC k (a->b) a' b' where
            toCcc f = build @k @a @b @a' @b' res where  -- build (Proxy :: Proxy labels) (Proxy :: Proxy b) res where
                    res = f val 
    
    toCcc' :: CCC k f a' b' => Proxy k -> f -> k a' b' 
    toCcc' _ f = toCcc f
    
    class Tag a where
        val :: a
    
    instance (IsTup a flag, Tag' a Z flag n) => Tag a where
        val = val' @a @Z @flag
    
    class Tag' a n (flag :: Bool) n'| a n flag -> n' where
        val' :: a
    
    instance (IsTup a flaga,
              IsTup b flagb,
              Tag' a n flaga n'',
              Tag' b n'' flagb n') => Tag' (a,b) n 'True n'  where
        val' = (val' @a @n @flaga, val' @b @n'' @flagb)
    
    instance (a ~ Leaf n) => Tag' a n 'False (S n)  where
        val' = Leaf
    
    
    type family Or a b where
        Or 'True b = 'True
        Or a 'True = 'True
        Or 'False 'False = 'False
    
    class In a b flag | a b -> flag where
    instance (
        ((a,b) == c) ~ isc, 
        flag' ~ Or flaga flagb, 
        flag ~ Or flag' isc,
        In a c flaga, 
        In b c flagb) => In (a,b) c flag
    instance ((Leaf n == c) ~ flag) => In (Leaf n) c flag
    
    
    class Build k input key a' b' | input key a' -> b' where
       build :: Cartesian k => key -> k a' b'
    
    instance ( 
        iseq ~ ((a,b) == key),
        In a key isinleft,
        In b key isinright,
        Cond k iseq isinleft isinright (a,b) key a' b'
        ) => Build k (a,b) key a' b' where
        build key = cond @k @iseq @isinleft @isinright @(a,b) @key @a' key
    
    instance (Leaf n ~ b, a' ~ b') => Build k (Leaf n) b a' b' where
        build _ = id
    
    
    class Cond k iseq isinleft isinright input key a b | iseq isinleft isinright input key a -> b where
        cond :: Cartesian k => key -> k a b
    -- Find the key is in the input
    instance (a ~ b) => Cond k 'True x x input key a b where
        cond _ = id
    instance (Build k a key a' c', (a',b') ~ ab) => Cond k 'False 'True x (a,b) key ab c' where -- get those input types inferred baby!
        cond key = (build @k @a @key @a' key) . fst
    instance (Build k b key b' c', (a',b') ~ ab) => Cond k 'False 'False 'True (a,b) key ab c' where
        cond key = (build @k @b @key @b' key) . snd
    
    -- Otherwise destruct on the key
    instance (Build k input key1 a' c', 
              Build k input key2 a' d') => Cond k 'False 'False 'False input (key1,key2) a' (c',d') where
        cond (key1,key2) = fan (build @k @input @key1 @a' key1) (build @k @input @key2 @a' key2)
    
    instance (Build k input key a' b',
        f ~ k b' c')
     => Cond k 'False 'False 'False input (App f key) a' c' where
        cond (App f key) = f . (build @k @input @key @a' key)
    
    -- Could I replace almost everything with App? A very powerful construct
    -- This is a of some relation to defunctionalization like in HList
    -- Maybe I should build a typelevel FreeCat and then do compilation passes on it
    
    {-
    type family (StripLeaf a) where
        StripLeaf (a,b) = (StripLeaf a, StripLeaf b)
        StripLeaf (Leaf n a) = a 
    -}
    
    
    
    
    
    




[![drawing-1](http://philzucker2.nfshost.com/wp-content/uploads/2018/08/Drawing-1.jpeg)](http://philzucker2.nfshost.com/wp-content/uploads/2018/08/Drawing-1.jpeg)




