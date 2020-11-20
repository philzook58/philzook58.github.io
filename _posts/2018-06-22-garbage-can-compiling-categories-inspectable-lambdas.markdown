---
author: philzook58
comments: true
date: 2018-06-22 14:25:50+00:00
layout: post
link: https://www.philipzucker.com/garbage-can-compiling-categories-inspectable-lambdas/
slug: garbage-can-compiling-categories-inspectable-lambdas
title: Garbage Can Compiling to Categories with Inspectable Lambdas
wordpress_id: 1104
---

There are a couple kinds of functions that we can turn into totally inspectable data.

Linear functions can be reconstituted into a matrix if you give a basis of vectors.

Functions from enumerable types can be turned into a lookup table

Sufficiently polymorphic functions are another example though. forall a. a-> a is commonly known to only be id. The same goes for fst = forall a b. (a,b)->a and snd and swap and all the nesting of . These functions have exactly one inhabiting value (excluding internal churning and the possibility of going into an infinite loop).

So the type directly tells us the implementation

forall a. (a,a)->a is similar. It can only be fst or snd. Types that reuse a type parameter in the input can only be permutations.

I've been trying to find a way to take a written lambda and convert it to data automatically and have been having trouble.

An opaque type that we have hidden the contructors to is the same (T,T)->T can only be fst or snd specialized to T since we can't possibly destruct on T.

We can figure out which one by giving a labeled example to that function and then inspecting a single output.  This gives the permutation and duplication that was done.

Similarly for T -> Either T T

Once we have this, we can (Hopefully) reinterpret this lambda in terms of a monoidal category.



    
    {-# LANGUAGE RankNTypes, GADTs, FlexibleInstances, 
    DataKinds, TypeFamilies,MultiParamTypeClasses,
    
    FlexibleContexts,
    
    ScopedTypeVariables,
    FunctionalDependencies,
    
    GADTs,
    TypeOperators
     #-}
    
    --AllowAmbiguousTypes,
    -- OverlappingInstances,
    -- UndecidableInstances,
    import Data.Proxy
    import Unsafe.Coerce
    
    
    data Tag = Tag Int deriving Show
    
    type family (MonoMorphTag a) :: * where
    	MonoMorphTag (a,b) = (MonoMorphTag a, MonoMorphTag b)
    	MonoMorphTag (a->b) = (MonoMorphTag a) -> (MonoMorphTag b)
    	MonoMorphTag Int = Int
    	MonoMorphTag [a] = [a]
    	MonoMorphTag (a,b,c) = (a,b,c)
    	MonoMorphTag (a,b,c,d) = (a,b,c,d)
    	MonoMorphTag Double = Double
    	MonoMorphTag () = ()
    	MonoMorphTag Char = Char
    	MonoMorphTag _ = Tag 
    
    unsafeMonoTag :: a -> MonoMorphTag a
    unsafeMonoTag = unsafeCoerce
    
    
    -- unsafeTagLeaves :: forall a. MonoMorphTag a -> Tag
    -- unsafeTagLeaves = unsafeCoerce
    
    type T = Tag
    
    class GetVal a where
      val :: Int -> Proxy a -> (a, Int)
    
    instance GetVal Tag where
    	val n _ = (Tag n, n+1)
    
    instance (GetVal a, GetVal b) => GetVal (a,b) where
    	val n _ = ((v1, v2), n'') where
    						(v1 , n') = val n (Proxy :: Proxy a) 
    						(v2 , n'') = val n' (Proxy :: Proxy b)
    
    data TagTree a = Node (TagTree a) (TagTree a) | Leaf a deriving Show -- | Apply (k a b) TagTree
    
    class Treeify a  b where
    	treeify :: a -> TagTree b
    
    instance Treeify Tag Tag where
    	treeify x = Leaf x
    
    instance (Treeify a Tag, Treeify b Tag) => Treeify (a,b) Tag where
    	treeify (a,b) = Node (treeify a) (treeify b)
    
    class MonoMorph a where
    	type Mono a :: *
    
    instance MonoMorph (a,b) where
    	type Mono (a,b) = (Mono a, Mono b)
    {-
    instance MonoMorph (MonoMorphTag a) where
    	type Mono a = Tag
    -}
    
    {-
    -- Hmm I'm not sure how to monomorhpize this.
    fst' :: (TagTup a) => (a, b) -> a
    fst' = fst
    -}
    {-
    class AutoCurry a b | a -> b where
    	autocurry :: a -> b 
    
    instance AutoCurry (a->b->Tag) ((a,b)->Tag) where
    	autocurry f = uncurry f
    
    instance AutoCurry c (a->c') => AutoCurry (b->c) ((b,a) -> c') where
    	autocurry f = uncurry (\b -> autocurry (f b))
    -}
    
    data Monoidal = Dup | Mon Monoidal Monoidal | Par Monoidal Monoidal | Fst | Snd | Id | Comp Monoidal Monoidal deriving Show
    
    data Monoidal' a b where
    	Id' :: Monoidal' a a
    	Dup' :: Monoidal' a (a,a)
    	Fst' :: Monoidal' (a,b) a
    	Snd' :: Monoidal' (a,b) b
    	Comp' :: Monoidal' b c -> Monoidal' a b -> Monoidal' a c
    	Mon' :: Monoidal' a a' -> Monoidal' b b' -> Monoidal' (a,b) (a',b')
    
    
    data FunData = FunData {inval :: TagTree Tag, outval :: TagTree Tag} deriving Show
    
    class TestIdea a b where
    	works :: (a -> b) -> (a, b)
    
    instance (GetVal a) => TestIdea a b where
    	works f = (inval,  f inval) where inval = fst $ val 0 (Proxy :: Proxy a) -- fst $ val 0 (Proxy :: Proxy b)
    
    fuckmyshitup :: (GetVal a, Treeify a Tag, Treeify b Tag) => (a -> b) -> FunData
    fuckmyshitup f = let (a, b) = works f in FunData ((treeify a) :: TagTree Tag) ((treeify b):: TagTree Tag) 
    
    ccc :: FunData -> Monoidal
    ccc (FunData x (Node y z)) = Mon (ccc $ FunData x y) (ccc $ FunData x z)
    ccc (FunData (Leaf _) (Leaf _)) = Id
    ccc (FunData (Node x y) z@(Leaf (Tag n))) = if inleft n x then Comp Fst (ccc (FunData x z)) else Comp Snd (ccc (FunData y z))
    
    
    ineither :: Int -> TagTree Tag -> Bool
    ineither n (Node x y) = (ineither n x) || (ineither n y)
    ineither n (Leaf (Tag n')) = n == n'
    
    inleft :: Int -> TagTree Tag -> Bool
    inleft n (Node l r) = ineither n l
    inleft n (Leaf (Tag n')) = n == n'
    
    inright :: Int -> TagTree Tag -> Bool
    inright n (Node l r) = ineither n r
    inright n (Leaf (Tag n')) = n == n'
    
    -- Then we can compile to categories. Replacing the entire structure with dup and par and
    -- fst, snd, etc.
    
    -- Make an infix operator $'
    --data Apply k a b c = Apply (FreeCat k a b) c
    --type ($$) = Apply
    -- No, don't need getval.
    -- We'll just need it for treeify?
    {-instance GetVal c => GetVal (Apply k a b c) where
    	val n _ = where x, n' = val n Proxy c
    -}
    -- Another Option
    
    data A
    data B
    data C
    
    -- This is basically a lambda calculus
    -- I could probably finitely enumerate through all the typeclasses for all the variables
     
    example = Proxy :: Proxy ((A,B) -> B)
    
    -- Hmm this would allow you to force duplicate input types though.
    
    {-
    class (Tagify a ~ a, Tagify b ~ b) => TestIdea a b where
    	works :: (a -> b) -> (a, b)
    
    instance (GetVal a) => TestIdea a b where
    	works f = (inval,  f inval) where inval = fst $ val 0 (Proxy :: Proxy a) -- fst $ val 0 (Proxy :: Proxy b)
    -}
    --thisworks :: String
    --thisworks = works id
    
    -- fst . (val 0)
    
    {-
    instance (F a ~ flag, GetVal' flag a) => GetVal a where
      val = val' (Proxy :: Proxy flag)
    
    class GetVal' (flag :: Bool) a where
      val' :: Proxy flag -> a -> Tagify a
    
    instance (GetVal a, GetVal b) => GetVal' 'True (a,b) where
      val' _ (x,y) = (val x, val y)
    
    instance GetVal' 'False a where
      val' _ x = Tag 0
    -}
    
    




What about TH? Also the new quantified constraints extensions might be helpful?





Ok. A Different approach. This works much better to what I had in mind. you can write aribatrary (\(x,y,) -> (y,x)) tuple like lambdas and it will convert them to a category. I really had to hack around to get the thing to compile. Like that Pick typeclass, what the heck? Why can I get defaults values in type families but not in typeclasses?

It is all decidedly not typesafe. You can get totally nonsensical things to compile to something. However if you stick to lambdas, you'll be ok. Maybe.

No on further review this does not work. I got tricked that the type seemed ok at a certain point.  A couple problems arise upon actual application. Since the idea is to drive the form based on the type variables upon actual application to something that has types of the same form it gets all screwed up. Also tons of instances are overlapping, although I think this is fixable.

Maybe what I need is existential types that can't ever unify together accidentally.

A couple thought on typelevel programming principles:



 	
  1. Typeclasses are hard to get default cases. You want to use type families if that is what you want

 	
  2. Typeclasses need unique stuff to appear on the right hand side. Only 1 pattern should match. You might need to add extra parameters to match to which you can force on the left hand side of the instance

 	
  3. ~ type equality is real useful

 	
  4. 



An alternative to using lambda is to use an explicit Proxy. The type variables are basically just as good for syntactic purposes (a touch more noisy).

    
    {-# LANGUAGE RankNTypes, GADTs, FlexibleInstances, 
    DataKinds, TypeFamilies,MultiParamTypeClasses,
    ImpredicativeTypes,
    
    FlexibleContexts,
    
    ScopedTypeVariables,
    FunctionalDependencies,
    UndecidableInstances,
    GADTs,
    TypeOperators
    
     #-}
    
    -- OverlappingInstances, NoImplicitPrelude
    --
    --UndecidableInstances,
    --OverlappingInstances,
    
    import Data.Type.Bool
    import Data.Proxy
    --import Control.Category
    --import GHC.Base hiding (id,(.))
    
    class IsId a where
    	val :: a -> a
       -- toCat 
    instance forall a. IsId (a -> a) where
        val _ = id
    
    {-
    class Catable f a b | f -> a,b where
    	toCat :: forall k. CartesianCategory k => k a b
    
    instance forall a b. Catable ((a,b)->a) (a,b) a where
    	toCat = fst
    -}
    class Fst ab a | ab -> a where
    --   toCat :: forall k. k ab a
    instance forall a b. Fst (a,b) a
    
    
    
    class Anything b where
       fun :: b -> b 
    
    class Stringly a where
    	stringly :: a -> String
    
    instance (Stringly a, Stringly b) => Stringly (a,b) where
       stringly (x,y) = "(" ++ (stringly x) ++ "," ++ (stringly y) ++ ")"
    {-
    instance (Stringly a, Stringly b) => Stringly (a -> b) where
       stringly f = "(" ++ (stringly x) ++ "->" ++ (stringly y) ++ ")"
    -}
    
    class Category k where
    	dot' :: k b c -> k a b -> k a c
    	id' :: k a a
    
    instance Category (->) where
    	dot' = (.)
    	id' = id
    
    class Category k => CartesianCat k where
    	fst' :: k (a,b) a
    	snd' :: k (a,b) b
    	join' :: k a b -> k a c -> k a (b,c) 
    
    
    instance CartesianCat (->) where
    	fst' = fst
    	snd' = snd
    	join' = join''
    
    class Catable a b where
    	toCat :: CartesianCat k => (a -> b) -> (k a b)
    --  toCat (\x -> ((x,x),x))  . id
    
    -- it's not INSANE to just list out a finite list of possibilities ((a,b),c) etc.
    
    
    {-
    data HeldApply k a b = HeldApply (k a b) a
    
    
    ($$) :: Category k => k a b -> b -> HeldApply k a b
    f $$ x = HeldApply f
    
    instance Catable a (HeldApply a b) where
    	toCat 
    Doesn't seem to work. We don't have an a get get the heldapply out of the function
    
    Maybe we could pass in the approriate function as a a lambda \f x -> Apply f x
    
    
    instance ExponentialCategory k where
    	apply :: k (k a b, a) b  
    
    -}
    
    
    instance Catable a a where
    	toCat _ = id'
    -- why is this okay? should these be covered by the other cases?
    instance Catable (a,b) a where
    	toCat _ = fst'
    
    instance Catable (a,b) b where
    	toCat _ = snd'
    
    dup x = (x,x)
    
    {-
    instance Catable a (a,a) where
    	toCat _ = dup
    -}
    join'' f g x = (f x, g x)
    -- iterates down through the output
    instance (Catable a b, Catable a c) => Catable a (b,c) where
    	toCat f = join' (toCat (fst . f)) (toCat (snd . f))
    {-
    instance (InL c (a,b), Catable a c) => Catable (a,b) c where
    	toCat f = (toCat (f . fst))
    
    instance (InR c (a,b), Catable a c) => Catable (a,b) c where
    	toCat f = (toCat (f . snd))
    -}
    instance (Catable a c, Catable b c, Pick' c (a,b) (In a c)) => Catable (a,b) c where
    	toCat f = pick' (Proxy :: Proxy (In a c))
    
    {-
    instance (Catable a c, Catable b c, Pick c (a,b) (In a c)) => Catable (a,b) c where
    	toCat f = (toCat (pick (Proxy :: Proxy (In a c))))
    -}
    {-
    class In a c where
    	find :: c -> a
    
    instance In a a
       find = id
    instance In a b => In a (b,c)
       find = find . fst
    instance In a c => In a (b,c)
       find = find . snd
    -}
    
    
    {-
    type family (LorR a c) :: Nat where
    	LorR a (a,_) = 1
    	LorR a (_,a) = 2
    	LorR a ((b,c),d) = (LorR a (b,c)) + (LorR a d)
    	LorR a (d,(b,c)) = (LorR a (b,c)) + (LorR a d)
    	LorR a _ = 0
    -}
    
    type family (In a c) :: Bool where
    	In a a = 'True
    	In a (a,_) = 'True
    	In a (_,a) = 'True
    	In a ((b,c),d) =  In a (b,c) || In a d 
    	In a (d,(b,c)) = In a (b,c) || In a d 
    	In a _ = 'False
    
    
    
    {-
    type Snd = forall a b. (a,b) -> b
    
    type family (FstSnd a) :: * where
    	FstSnd 'True = Snd
    	FstSnd 'False = Snd
    -}
    
    class Pick a c (d :: Bool) where
    	pick :: Proxy d -> c -> a
    
    instance (Pick a (e,f) (In a e), (e,f) ~ b) => Pick a (b,c) 'True where
    	pick _ = (pick (Proxy :: Proxy (In a e))) . fst
    
    instance (Pick a (e,f) (In a e), (e,f) ~ c) => Pick a (b,c) 'False where
    	pick _ = (pick (Proxy :: Proxy (In a e))) . snd
    
    instance Pick a (a,b) 'True where
    	pick _ = fst
    
    instance Pick a (b,a) 'False where
    	pick _ = snd
    
    instance Pick a a d where
    	pick _ = id
    
    -- The bool is true if in the left branch
    class Pick' a c (d :: Bool) where
    	pick' :: CartesianCat k => Proxy d -> k c a
    
    instance (Pick' a (e,f) (In a e), (e,f) ~ b) => Pick' a (b,c) 'True where
    	pick' _ = dot' (pick' (Proxy :: Proxy (In a e))) fst'
    
    instance (Pick' a (e,f) (In a e), (e,f) ~ c) => Pick' a (b,c) 'False where
    	pick' _ = dot' (pick' (Proxy :: Proxy (In a e))) snd'
    
    instance Pick' a (a,b) 'True where
    	pick' _ = fst'
    
    instance Pick' a (b,a) 'False where
    	pick' _ = snd'
    
    instance Pick' a a d where
    	pick' _ = id'
    
    
    
    {-
    class InL a c where
    
    instance InL a a
    instance In a b => InL a (b,c)
    
    class InR a c 
    instance InR a a
    instance In a b => InR a (c,b) 
    -}
    
    {-
    
    instance (Catable a c, Catable b c) => Catable (a,b) c where
    	toCat f = 
    
    instance (Catable a c, Catable b c) => Catable a (b,c) where
    	toCat f = 
    -}
    
    {-
    instance (Stringly a, Stringly b, (a,b) ~ c, IsTup c ~ 'True) => Stringly c where
       stringly (x,y) = "(" ++ (stringly x) ++ "," ++ (stringly y) ++ ")"
    -}
    
    --instance (IsTup a ~ 'False, IsArr a ~ 'False) => Stringly a where
    --	stringly _ = "_"
    
    
    
    instance forall a. Anything a where
    	fun = id
    
    example :: a -> a
    example = val id
    
    type family (IsTup a) :: Bool where
    	IsTup (a,b) = 'True
    	IsTup _ = 'False
    
    type family (IsArr a) :: Bool where
    	IsArr (a->b) = 'True
    	IsArr _ = 'False
    





