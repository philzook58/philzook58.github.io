---
author: philzook58
comments: true
date: 2018-08-20 03:39:41+00:00
layout: post
link: https://www.philipzucker.com/?p=1194
published: false
slug: Infinite Differentiation in Haskell and applications to Perturbative path integrals
title: Infinite Differentiation in Haskell and applications to Perturbative path integrals
wordpress_id: 1194
---

here is my garbage.

index multiplication can be replaced by function composition.

There are two levels of things here that can get cloudy. One really should see x and dx as objects only to be mixed carefully.

Doug McEllroy's powser

Conal Elliott's Automatic Differentiation Made Easy

There is a choice here: do I actually deal with the typeclasses necessary to make things more generic?

    
    
    data Powser f b = More b (f (Powser f b))
    
    data Powser a b = More b (a -> Powser f b)
    
    instance Functor (Powser a) where
       fmap (More b )
    
    
    data Powser a b = More (a->(b, a->Powser a b) 
    -- powser is an infinitely forward differetiable function, using a function representation for tensors
    data Powser a b = More (a->b) (a -> Powser a b) | Zero
    
    
    
    
    Powser a b = CoFree ((->) a) b
    
    
    --par (More b f) (More c g) = More (b,c) (\(x,y) -> par (f x) (g y))
    par (More b f) (More c g) = More (b *** c) (\(x,y) -> par (f x) (g y))
    -- linear functions do not have higher derivatives
    
    dup :: Powser dx (dx,dx)
    dup = More \x -> (x,x) Done -- (const dup) -- or Done  -- higher derivatives are all zero
    
    fst :: Powser (dx,dy) dx
    fst = More fst Done
    
    snd = More snd Done
    
    
    
    plus :: Num a => Powser (a,a) a
    plus = More (\(x,y)-> x + y) Done -- curry (+)
    
    
    --times :: Num a => Powser (a,a) (a,a) -- uhhhh. No. Non nononononononono. There is no sensible instance of Powser
    --times = More (\(x,y) -> (y, x))  Done -- (\(x,y) -> )
    
    times :: DFun (a,a) a da db 
    times (x,y) = (x*y, More (\(dx,dy) -> (dx*y + dy * x) (\(dx1, dy1) -> More (\(dx2,dy2) -> dx1*dy2 + dx2*dy1) (const Done))
    -- elementwise 
    pmap :: Functor f => Powser a b -> Powser (f a) (f b)
    pmap :: 
    
    
    
    -- Composition requires some strong properties.
    -- addition only. Because function composition holds an implciit multiplication, which is all we need. 
    comp :: Powser b c -> Powser a b -> Powser a c
    comp Done _ = Done
    comp _ Done = Done
    comp a@(More f l) b@(More g k) = More (f . g) (\x -> (plus  . par (comp a (k x))  (comp (l (g x)) b)) . dup) -- ?
    
    
    jZ = More (\j -> j * sigmax) (\j -> scale j jZ2)
    jZ2 = More \j -> j * eye) (\j -> scale j jZ) 
    hdt = More (\dx -> dx * exp i dt) Done
    
    twotimesteps :: Powser (J,J) M2
    twotimesteps = comp times (par jZ (scale hdt jZ)
    
    tts = twotimesteps
    ground :: Powser a M2 -> Powser a Double
    ground (More f g)= More (fmap (\m -> gs * m * gs) f)  (fmap ground g)  
    
    type Jt = (J,J)
    z2 :: Powser (Jt, Jt)  Double
    z2 = times . par z z where z = (ground tts)
    
    class Iterate
    
    -- memoize calculations in the store.
    type MPowser a b = (Store, Powser a b)
    -- or (m Powser a b)
    
    -- I feel vaguely that finally tagless might help. we need to build labels for computations, see if we already did them.
    
    
    type DFun a b da db = a -> (b, Powser da db)
    
    
    
    
    x + y =   (plus . par) x y
    x * y = (times . par) x y
    
    
    (More b f) . (More c g) = More b (f . g)  
    
    
     data M2 a = M2 a a a a
     data V2 a = V2 a a
    
     (M2 a b c d) *m (M2 e f g h) = M2 () () () ()
    
    
    instance Num a => Num (M2 a)
    
    SpinSeries = Powser Double (M2 Double)
    
    -- Let us assume J = 0? Does that help?
    
    
    -- At least three useful notions of mutiplication
    newvartimes :: Powser a b -> Power c b -> Powser (a,c) b -- Thjis is the one we need for mutiplying out new J matrices
    times :: Num a => Powser (a,a) a
    times' :: Powser a b -> Powser a b -> Powser a b
    scale :: b -> Powser a b -> Powser a b
    
    -- uncoupled SHO at each point.
    
    
    
    
    
    



