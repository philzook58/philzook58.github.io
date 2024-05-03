---
author: philzook58
comments: true
date: 2019-01-01 21:54:34+00:00
layout: post
link: https://www.philipzucker.com/?p=1589
published: false
slug: Categories 4
title: Categories 4
wordpress_id: 1589
---

quite amusingly, the Arrow typeclass is sometimes discussed as being exactly ome kinfd of strong profuntor or as some  cartesian cegatyr thing . The thing you don't have is arr, the function that converts ordinary functions to an arrow. It's supposed to be kind of like `return`. toCCC actually gives you a constrained implementation

Observable sharing might be a mechanism you can use you help optimize?

Inlining the entire interpretation function might be a way to force it to complete



I have a suspicion there is some kind of cps transform or some other way of structuring the construction that might help also. Some laziness with respect to  going all the way to the elements. My original version of type 2 had a similar problem and I found a way to help a little bit by searching for nodes and not just leaves.



It's not clear that we are doing much of anything? You can already get some AD from polymorphic functions, interval arithmetic, other things. That's the beauty of polymorphism. Also different from Conal's approach we are not getting GHC optimizations for free. Maybe some. Rewrite rules might help.









    
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
         FlexibleContexts,
        ScopedTypeVariables,
        StandaloneDeriving,
        PartialTypeSignatures,
        GADTs #-}
    
    import Control.Category
    import Prelude hiding ((.), id)
    -- import Prelude (Bool(..))
    
    class IsTup a b | a -> b
    instance {-# INCOHERENT #-} (c ~ 'True) => IsTup (a,b) c
    instance {-# INCOHERENT #-} (b ~ 'False) => IsTup a b
    
    
    class Category k => Monoidal k where
        parC :: k a c -> k b d -> k (a,b) (c,d)
    
    class Monoidal k => Cartesian k where
        fstC :: k (a,b) a 
        sndC :: k (a,b) b 
        dupC :: k a (a,a) 
    
    fanC f g = (parC f g) . dupC
    
    
    class Cartesian k => NumCat k where
        addC :: Num a => k (a,a) a
        mulC :: Num a => k (a,a) a
        -- fomrInteger 
    
    {-
    class ApplyTo 
       applyto :: path -> (a -> b) -> c 
    
    instance ApplyTo   (a,b) c 'True where
        applyto path f = f . (applyto  (fstC . path)  ,  )
    -}
    {-
    class BuildInput tup flag where
        buildInput :: tup
    instance BuildInput (a,b) 'True where
        buildInput = (buildInput @a . fstC, buildInput @b . sndC)
    
    instance (Category k, a ~ k b b) => BuildInput a 'False where
        buildInput path = path
    -}
    
    {-
    buildInput' :: (Category k, BuildInput tup (k a a) (IsTup tup)) => tup
    buildInput' = buildInput idC
    
    -}
    
    {-
    
    Description:
    
    We are still taking polymophic functions.
    
    In this case the type of the function does not fully sepcify the implementation. Because the path is tracked in the input, even if stuff unifies together it is still fine
    
    
    Can we lessen the dups? Some sort of cps transform?
    
    
    Every operation you use needs to be defined in terms of some cat typeclass. You need to define how that typeclass can be used in terms of 
    
    TODO: Implement Generics.
    What about structures? Lists, etc. Maybe we need to put them in Fix form?
    
    
    Problems: BoolCat is no good. We aren't going to be able to override the standard boolena operations. They aren't polymorphic enough
    Same goes fo some other standard operations. :(
    Maybe you can use the fact that Bool only has finite values to build a truth table and hack it in
    
    Questions: Are we basically using HOAS? Finally Tagless style? Kind of. The trick of being able to use raw fst makes it a bit different.
    
    
    
    -}
    
    
    idC :: Category k => k a a
    idC = id
    
    -- path is kind of a lens. It is an accessor
    -- extending this to Sum types does not seem like a problem?
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
    
    
    
    
    {-
    instance CCC 
       toCCC f = 
                      where
                       input = buildInput @stuff
                       output = f input 
    -}
    
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
    toCCC f = fanOutput @b @fb output where  --fanOutput @b @fb (f (buildInput @a @fa (idC @k @x))) 
                                          -- input :: _
                                          input = buildInput @a @fa (idC @k @a')
                                          -- output :: _
                                          output = f input
    
    
    
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
    
    instance NumCat FreeCat where
        addC = Add
        mulC = Mul
    
    -- So do you ever want to add together things that have different codomain objects z? Doesn't super makes sense.
    {-
    Eq a => EqCat (k z a)
     eqC :: k (a,a) Bool
    
    Eq' :: a -> a -> Bool
    
    Oh! Actually we're in trouble on Num also. We need to constraint b to be a Num. We need constrained categories
    
    EqCat k
    
    (a,a) Bool
    
    
    -- lifting is often like lifting on function types
    -- There is a Num instance for functions
    -- But no Eq or Ord
    
    -- Bool is a Cocartesian type
    
      iteC Bool f g? Needs  
    
    
    
    Eq a => Eq (k z a)
      == eqC . fanC f g
    
    
    (k z a) where
         -> 
    -}
    
    instance (NumCat k, Num a) => Num (k z a) where
        f + g = addC . (fanC f g)
        f * g = mulC . (fanC f g)
        signum = error "NO"
        fromInteger = error "NO"
        (-) = error "NO"
        abs = error "No"
    
    
    {-
    , k 
    
    
    -}
    
    --example1 :: forall k a b fa fb x. (IsTup a fa, Cartesian k, BuildInput a fa (k x x)) => (a -> b) -> k a b
    --example1 f = (f (buildInput @a @fa (idC @k @x))
    
    example2 = toCCC @FreeCat (\(x,y)->(y,x))
    
    --example3 :: FreeCat (a,(b,c)) c
    -- example3 = toCCC @FreeCat (\(z,y)->(z,z))
    --example3 :: Cartesian k => k _ _
    -- example3 = toCCC (\(z,y)->(z,z))
    
    example4 = toCCC @FreeCat (\((x,y),z) -> x)
    -- example4 :: Cartesian k => k _ _
    -- example4 = toCCC (\((z,y),x)->x)
    
    example5 = toCCC @FreeCat (\(x,y) -> x + y)
    example6 = toCCC @FreeCat (\(x,y) -> y + (x * y))
    
    
    --example2 :: forall a b a' b' (flag :: Bool). IsTup (a,b) flag => (FreeCat (a',b') a', FreeCat (a',b') b')
    --example2 = buildInput @(a,b) @flag idC
    
    example1 :: forall a' (flag :: Bool). (IsTup (FreeCat a' a') flag,  BuildInput (FreeCat a' a') flag (FreeCat a' a')) => FreeCat a' a'
    example1 = buildInput @(FreeCat a' a') @flag (idC @FreeCat @a')
    
    -- example2 :: IsTup a (flag :: Bool) => Maybe flag -> Maybe flag
    -- example2 = id
    
    
    --example1 = toCCC @FreeCat id
    
    {- REWRITE (fst *** snd) . dup = id -}
    
    {-
    instance (AdditiveCategory k, Num b) => Num (k a b)
       f + g = plusC . (fan f g)
    
       -}


Some kind of CPS transfromation. Maybe i actually want lens? Maybe I want the leaves to be some kind of function not just the pure morphism. Like a function with slots for putting morphism in between the levels.  ((()()) -> ()() ) ->( ()() -> ()    ) ->()

(a -> b) -> (b -> c) -> (c -> d)

(a -> a) -> (b -> b) -> (c -> c) -- in level morphisms.

() -- deep cps.





The previous version was entirely type directed.



-----------



App is interesting. I need to build bigger programs to see what I need. Is my approach actually composable.

CCC is kind of the definition of a Functor. (->) => k

Could write endofunctor in similar form.

Case val (\x -> ) could be useful for deconstructing returned value of literals. Or call it let?

We really do need to build a full syntax tree at the type-level I think. It is unfortunate that I can't use

App f a n = App f a. Use phantom parameter for identity. Then we can use native let expressions. and just share the computation.

Using toCCC within an App context. Can we bring variables into scope in there?

Different kinds of App? AppLiteral, AppContinuation?

Doing the construction in CPS may be helpful. forall r. k a r -> k b r

Search for optimality?

Add in CoCartesian Either deconstruction, and Closed (->).

Generics

Relation to Finally Tagless Staged Interpreters? The Cartesian classes themselves feel close to finally tagless style (free extensionality). My FreeCats are the initial style.

Vectors. There is a monoidal instance for kron. Gives us the ability to write matrix multiplication as application without sacrificing ability to tranpose or invert.

Vector spaces do have currying. They are closed but not cartesian (we have no dup and no fst/ snd if we consider the product to be kron).

Maybe Diag is interesting? It is kind of a way to lift a to (a,a), or (a,a) -> a






