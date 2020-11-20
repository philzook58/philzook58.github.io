---
author: philzook58
comments: true
date: 2018-12-27 04:31:15+00:00
layout: post
link: https://www.philipzucker.com/compiling-to-categories-3-a-bit-cuter/
slug: compiling-to-categories-3-a-bit-cuter
title: 'Compiling to Categories 3: A Bit Cuter'
wordpress_id: 1219
categories:
- Haskell
tags:
- Category Theory
- haskell
---

Ordinary Haskell functions form a cartesian closed category. Category means you can compose functions. Cartesian basically means you can construct and deconstruct tuples and Closed means that you have first class functions you can pass around.

[![](http://philzucker2.nfshost.com/wp-content/uploads/2018/08/Drawing-1.jpeg)](http://philzucker2.nfshost.com/wp-content/uploads/2018/08/Drawing-1.jpeg)

[Conal Elliott's Compiling to Categories](http://conal.net/papers/compiling-to-categories/) is a paradigm for reinterpreting ordinary functions as the equivalent in other categories. At an abstract level, I think you could describe it as a mechanism to build certain natural law abiding Functors from Hask to other categories. It's another way to write things once and have them run many ways, like polymorphism or generic programming. The ordinary function syntax is human friendly compared to writing raw categorical definitions, which look roughly like point-free programming (no named variables). In addition, by embedding it as a compiler pass within GHC, he gets to leverage existing GHC optimizations as optimizations for other categories. Interesting alternative categories include the category of graphs, circuits, and automatically differentiable functions. You can find his implementation[ here](https://github.com/conal/concat)

I've felt hesitance at using a GHC plugin plus I kind of want to do it in a way I understand, so I've done different versions of this using relatively normal Haskell (no template haskell, no core passes, but a butt ton of hackery).

The[ first](http://www.philipzucker.com/shit-compiling-categories-using-type-level-programming-haskell/) used explicit tags. Give them to the function and see where they come out. That is one way to probe a simple tuple rearrangement function.

The [second](http://www.philipzucker.com/approximating-compiling-categories-using-typelevel-haskell-take-2/) version worked almost entirely at the typelevel. It worked on the observation that a completely polymorphic tuple type signature completely specifies the implementation. You don't have to look at the term level at all. It unified the polymorphic values in the input with a typelevel number indexed Tag type. Then it searched through the input type tree to find the piece it needed. I did end up passing stuff in to the term level because I could use this mechanism to embed categorical literals. The typeclass hackery I used to achieve this all was heinous.

I realized today another way related to both that is much simpler and fairly direct. It has some pleasing aesthetic properties and some bad ones. The typeclass hackery is much reduced and the whole thing fits on a screen, so I'm pleased.

Here are the basic categorical definitions. FreeCat is useful for inspection in GHCi of what comes out of toCCC.

    
    {-# LANGUAGE GADTs, StandaloneDeriving, NoImplicitPrelude, FlexibleInstances  #-}
    
    module Cat where
    import Control.Category
    import Prelude hiding ((.), id)
    
    
    class Category k => Monoidal k where
        parC :: k a c -> k b d -> k (a,b) (c,d)
    
    
    class Monoidal k => Cartesian k where
        fstC :: k (a,b) a 
        sndC :: k (a,b) b 
        dupC :: k a (a,a) 
    
    fanC f g = (parC f g) . dupC
    
    idC :: Category k => k a a
    idC = id
    
    data FreeCat a b where
        Comp :: FreeCat b c -> FreeCat a b -> FreeCat a c
        Id :: FreeCat a a
        Fst :: FreeCat (a,b) a
        Snd :: FreeCat (a,b) b
        Dup :: FreeCat a (a,a)
        Par :: FreeCat a b -> FreeCat c d -> FreeCat (a,c) (b,d)
        Add :: FreeCat (a,a) a
        Mul :: FreeCat (a,a) a
    
    deriving instance Show (FreeCat a b)
    
    instance Category FreeCat where
        (.) = Comp
        id = Id
    
    instance Monoidal FreeCat where
        parC = Par
    
    instance Cartesian FreeCat where
        fstC = Fst
        sndC = Snd
        dupC = Dup
    
    instance Monoidal (->) where
        parC f g = \(x,y) -> (f x, g y)  
    
    instance Cartesian (->) where
        fstC (x,y) = x
        sndC (x,y) = y
        dupC x = (x,x)
    
    class Cartesian k => NumCat k where
        mulC :: Num a => k (a,a) a
        negateC :: Num a => k a a
        addC :: Num a => k (a,a) a
        subC :: Num a => k (a,a) a
        absC :: Num a => k a a
    
    instance NumCat (->) where
        mulC = uncurry (*)
        negateC = negate
        addC = uncurry (+)
        subC = uncurry (-)
        absC = abs
    
    instance NumCat FreeCat where
        mulC = Mul
        negateC = error "TODO"
        addC = Add
        subC = error "TODO"
        absC = error "TODO"
    
    instance (NumCat k, Num a) => Num (k z a) where
        f + g = addC . (fanC f g)
        f * g = mulC . (fanC f g)
        negate f = negateC . f
        f - g = subC . (fanC f g)
        abs f = absC . f 
        signum = error "TODO"
        fromInteger = error "TODO"
    
    


And here is the basic toCCC implementation

    
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
         toCCC )where
    
    import Control.Category
    import Prelude hiding ((.), id)
    import Cat
    
    
    class IsTup a b | a -> b
    instance {-# INCOHERENT #-} (c ~ 'True) => IsTup (a,b) c
    instance {-# INCOHERENT #-} (b ~ 'False) => IsTup a b
    
    
    class BuildInput tup (flag :: Bool) path where
        buildInput :: path -> tup
    
    instance (Cartesian k,
              IsTup a fa,
              IsTup b fb,
              BuildInput a fa (k x a'), 
              BuildInput b fb (k x b'),
              ((k x (a',b')) ~ cat)) =>  BuildInput (a,b) 'True cat where
        buildInput path = (buildInput @a @fa patha, buildInput @b @fb pathb) where
                     patha = fstC . path
                     pathb = sndC . path
    
    instance (Category k, a ~ k a' b') => BuildInput a  'False (k a' b') where
        buildInput path = path
    
    
    class FanOutput out (flag :: Bool) cat | out flag -> cat where
        fanOutput :: out -> cat
    
    instance (Cartesian k,
             IsTup a fa,
             IsTup b fb,
             FanOutput a fa (k x a'),
             FanOutput b fb (k x b'),
             k x (a', b') ~ cat
             )
              => FanOutput (a, b) 'True cat where
        fanOutput (x,y) = fanC (fanOutput @a @fa x) (fanOutput @b @fb y)
    
    instance (Category k, kab ~ k a b) => FanOutput kab 'False (k a b) where
        fanOutput f = f 
    
    toCCC :: forall k a b a' b' fa fb x. (IsTup a fa, IsTup b fb, Cartesian k, BuildInput a fa (k a' a'), FanOutput b fb (k a' b')) => (a -> b) -> k a' b'
    toCCC f = fanOutput @b @fb output where
                                          input = buildInput @a @fa (idC @k @a')
                                          output = f input
    
    
    




Here is some example usage

    
    example2 = toCCC @FreeCat (\(x,y)->(y,x))
    
    -- You need to give the type signature unfortunately if you want polymorphism in k. k is too ambiguous otherwise and makes GHC sad.
    example3 :: Cartesian k => k _ _
    example3 = toCCC (\(z,y)->(z,z))
    
    example4 = toCCC @FreeCat (\((x,y),z) -> x)
    
    example5 = toCCC @FreeCat (\(x,y) -> x + y)
    
    example6 = toCCC @FreeCat (\(x,y) -> y + (x * y))
    
    example7 :: Cartesian k => k _ _
    example7 = toCCC (\(x,(y,z)) -> (x,(y,z)))




What we do is generate a tuple to give to your function. The function is assumed to be polymorphic again but now not necessarily totally polymorphic (this is important because Num typeclass usage will unify variables). Once we hit a leaf of the input tuple, we place the categorical morphism that would extract that piece from the input. For example for the input type `(a,(b,c))` we pass it the value `(fstC ,(fstC . sndC, sndC . sndC ))`. Detecting when we are at a leaf again requires somehow detecting a polymorphic location, which is a weird thing to do. We use the Incoherent IsTup instance from [last time](http://www.philipzucker.com/approximating-compiling-categories-using-typelevel-haskell-take-2/) to do this. It is close to being safe, because we immediately unify the polymorphic variable with a categorial type, so if something goes awry, a type error should result. We could make it more ironclad by unifying immediately to something that contains the extractor and a user inaccessible type.

We apply the function to this input. Now the output is a tuple tree of morphisms. We recursively traverse down this tree with a `fanC` for every tuple. This all barely requires any typelevel hackery. The typelevel stuff that is there is just so that I can traverse down tuple trees basically.

One benefit is that we can now use some ordinary typeclasses. We can make a simple implementation of Num for (k z a) like how we would make it for (z -> a). This let's us use the regular `(+)` and `(*)` operators for example.

What is not good is the performance. As it is, the implementation takes many global duplication of the input to create all the `fanC`s. In many categories, this is very wasteful.This may be a fixable problem, either via passing in more sophisticated objects that just the bare extraction morphisms to to input (CPS-ified? Path Lists?) or via the GHC rewrite rules mechanism. I have started to attempt that, but have not been successful in getting any of my rewrite rules to fire yet, because I have no idea what I'm doing. If anyone could give me some advice, I'd be much obliged. You can check that out [here](https://github.com/philzook58/not-bad-ccc/blob/18757b272508fafd4ab2dc396b234fb2551f83f4/src/CCC.hs). For more on rewrite rules, check out the [GHC user manual](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#rewrite-rules) and this excellent tutorial by Mark Karpov [here](https://www.stackbuilders.com/tutorials/haskell/ghc-optimization-and-fusion/).

Another possibility is to convert to FreeCat, write regular Haskell function optimization passes over the FreeCat AST and then interpret it. This adds interpretation overhead, which may or may not be acceptable depending on your use case. It would probably not be appropriate for automatically differentiable functions, but may be for outputting circuits or graphs.

    
    interp (Comp f g) = (interp f) . (interp g)
    interp FstC = fstC
    interp Dup = dupC
    interp (Par f g) = parC (interp f) (interp g)
    -- etc




Another problem is dealing with boolean operations. The booleans operators and comparison operators are not sufficiently polymorphic in the Prelude. We could define new operators that work as drop in replacements in the original context, but I don't really have the ability to overload the originals. It is tough because if we do things like this, it feels like we're really kind of building a DSL more than we are compiling to categories. We need to write our functions with the DSL in mind and can't just import and use some function that had no idea about the compiling to categories stuff.

I should probably just be using Conal's concat project. This is all a little silly.
