---
author: philzook58
comments: true
date: 2019-01-28 04:47:31+00:00
layout: post
link: https://www.philipzucker.com/bidirectional-applicative-programming-and-automatic-differentation/
slug: bidirectional-applicative-programming-and-automatic-differentation
title: Applicative Bidirectional Programming and Automatic Differentiation
wordpress_id: 1700
categories:
- Haskell
tags:
- automatic differentiation
- haskell
- lens
---




I got referred to an interesting paper by a [comment of /u/syrak](https://www.reddit.com/r/haskell/comments/adgdyj/pointful_from_pointfree_has_this_been_done_before/edhupmi/).







[http://www2.sf.ecei.tohoku.ac.jp/~kztk/papers/kztk_jfp_am_2018.pdf](http://www2.sf.ecei.tohoku.ac.jp/~kztk/papers/kztk_jfp_am_2018.pdf)







_Applicative bidirectional programming_ ([PDF](http://www2.sf.ecei.tohoku.ac.jp/~kztk/papers/kztk_jfp_am_2018.pdf)), by Kazutaka Matsuda and Meng Wang







In it, they use a couple interesting tricks to make Lens programming more palatable. Lens often need to be be programmed in a point free style, which is rough, but by using some combinators, they are able to program lenses in a pointful style (with some pain points still left over). It is a really interesting, well-written paper. Lots 'o' Yoneda and laws. I'm not doing it justice. Check it out!







A while back I noted that [reverse mode auto-differentiation has a type very similar to a lens](http://www.philipzucker.com/reverse-mode-differentiation-is-kind-of-like-a-lens-ii/) and in fact you can build a working reverse mode automatic differentiation DSL out of lenses and lens-combinators. Many things about lenses, but not all, transfer over to automatic differentiation. The techniques of Matsuda and Wang do appear to transfer fairly well.







This is interesting to me for another reason. Their `lift2` and `unlift2` functions remind me very much of[ my recent approach to compiling to categories](http://www.philipzucker.com/compiling-to-categories-3-a-bit-cuter/). The `lift2` function is fanning a lens pair. This is basically what my FanOutput typeclass automated. `unlift2` is building the input for a function function by supplying a tuple of projection lenses. This is what my BuildInput typeclass did. I think their style may extend many monoidal cartesian categories, not just lenses.






    
    <code>lift2 :: Lens (a,b) c -> (forall s. Num s => (Lens s a, Lens s b) -> Lens s c)
    lift2 l (x,y) = lift l (fan x y)
    
    unlift2 :: (Num a, Num b) => (forall s. Num s => (Lens s a, Lens s b) -> Lens s c) -> Lens (a,b) c
    unlift2 f = f (fst', snd')</code>







One can use the function `b -> a` in many of the situations one can use `a` in. You can do elegant things by making a Num typeclass of `b -> a` for example. This little fact seems to extend to other categories as well. By making a Num typeclass for `Lens s a` when `a` is a Num, we can use reasonable looking notation for arithmetic.






    
    <code>t1 :: Num a => Lens (a,a) a
    t1 = unlift2 $ \(x,y) -> x + y*y + y * 7</code>







They spend some time discussing the necessity of a Poset typeclass. For actual lawful lenses, the `dup` implementation needs a way to recombine multiple adjustments to the same object. In the AD-lens case, dup takes care of this by adding together the differentials. This means that everywhere they needed an Eq typeclass, we can use a Num typeclass. There may be usefulness to building a wrapped type `data NZ a = Zero | NonZero a`  like their Tag type to accelerate the many 0 values that may be propagating through the system.







Unfortunately, as is, the performance of this is abysmal. Maybe there is a way to fix it? Unlifting and lifting destroys a lot of sharing and often necessitates adding many redundant zeros. Why are you doing reverse mode differentiation unless you care about performance? Forward mode is simpler to implement. In the intended use case of Matsuda and Wang, they are working with actual lawful lenses, which have far less computational content than AD-lenses. Good lawful lenses should just be shuffling stuff around a little. Maybe one can hope GHC is insanely intelligent and can optimize these zeros away. One point in favor of that is that our differentiation is completely pure (no mutation). Nevertheless, I suspect it will not without help. Being careful and unlifting and lifting manually may also help. In principle, I think the Lensy approach could be pretty fast (since all it is is just packing together exactly what you need to differentiate into a data type), but how to make it fast while still being easily programmable? It is also nice that it is pretty simple to implement. It is the simplest method that I know of if you needed to port operable reverse mode differentiation to a new library (Massiv?) or another functional language (Futhark?). And a smart compiler really does have a shot at finding optimizations/fusions.







While I was at it, unrelated to the paper above, I think I made a working generic auto differentiable fold lens combinator. Pretty cool. `mapAccumL` is a hot tip.







For practical Haskell purposes, all of this is a little silly with the good Haskell AD packages around, the most prominent being







[http://hackage.haskell.org/package/ad](http://hackage.haskell.org/package/ad)







It is somewhat interesting to note the similarity of type `forall s. Lens s` appearing in the Matsuda and Wang approach to those those of the `forall s. BVar s` monad appearing in the backprop package. In this case I believe that the `s` type variable plays the same role it does in the ST monad, protecting a mutating Wengert tape state held in the monad, but I haven't dug much into it. I don't know enough about backprop to know what to make of this similarity.







[http://hackage.haskell.org/package/backprop](http://hackage.haskell.org/package/backprop)







The github repo with my playing around and stream of consciousness commentary is [here](https://github.com/philzook58/ad-lens/blob/master/src/Numeric/ADLens/AppBi.hs)






    
    <code class="language-haskell">{-# LANGUAGE NoImplicitPrelude, TypeSynonymInstances, RankNTypes #-}
    module Numeric.ADLens.AppBi where
    -- import Numeric.ADLens.Lens
    import Control.Category
    import Prelude hiding (id, (.))
    import Control.Arrow ((***))
    import Data.Functor.Const
    import Data.Traversable
    newtype Lens x y = Lens (x -> (y, y -> x)) 
    type L s a = Num s => Lens s a
    
    instance Category Lens where
      id = Lens (\x -> (x, id))
      (Lens f) . (Lens g) = Lens $ \x -> let (y, g') = g x in
                                               let (z, f') = f y in
                                               (z, g' . f') 
    
    
    
    grad'' (Lens f) x = let (y,j) = (f x) in j 1
    
    lift :: Lens a b -> (forall s. Lens s a -> Lens s b)
    lift l l' = l . l'
    
    unlift :: Num a => (forall s. Num s => Lens s a -> Lens s b) -> Lens a b
    unlift f = f id
    
    
    dup :: Num a => Lens a (a,a)
    dup = Lens $ \x -> ((x,x), \(dx,dy) -> dx + dy)
    
    par :: Lens a b -> Lens c d -> Lens (a,c) (b,d)
    par (Lens f) (Lens g) = Lens l'' where
        l'' (a,c) = ((b,d), f' *** g') where
            (b,f') = f a
            (d,g') = g c
    
    fan :: Num s => Lens s a -> Lens s b -> Lens s (a,b)
    fan x y = (par x y) . dup 
    
    -- impredicative polymorphism errror when we use L in type sig. I'm just going to avoid that.
    lift2 :: Lens (a,b) c -> (forall s. Num s => (Lens s a, Lens s b) -> Lens s c)
    lift2 l (x,y) = lift l (fan x y)
    
    unlift2 :: (Num a, Num b) => (forall s. Num s => (Lens s a, Lens s b) -> Lens s c) -> Lens (a,b) c
    unlift2 f = f (fst', snd')
    
    instance (Num a, Num b) => Num (a,b) where
    	(x,y) + (a,b) = (x + a, y + b)
    	(x,y) * (a,b) = (x * a, y * b)
    	abs (x,y) = abs (x,y)
    	fromInteger x = (fromInteger x, fromInteger x)
    	-- and so on
    
    fst' :: Num b => Lens (a,b) a
    fst' = Lens (\(a,b) -> (a, \ds -> (ds, 0)))
    
    snd' :: Num a => Lens (a,b) b
    snd' = Lens (\(a,b) -> (b, \ds -> (0, ds)))
    
    unit :: Num s => Lens s () -- ? This isn't right.
    unit = Lens (\s -> ((), const 0))
    
    add :: Num a => Lens (a,a) a 
    add = Lens $ \(x,y) -> (x + y, \ds -> (ds, ds))
    
    sub :: Num a => Lens (a,a) a 
    sub = Lens $ \(x,y) -> (x - y, \ds -> (ds, -ds))
    
    mul :: Num a => Lens (a,a) a 
    mul = Lens $ \(x,y) -> (x * y, \dz -> (dz * y, x * dz))
    
    recip' :: Fractional a => Lens a a 
    recip' = Lens $ \x-> (recip x, \ds -> - ds / (x * x))
    
    div :: Fractional a => Lens (a,a) a 
    div = Lens $ (\(x,y) -> (x / y, \d -> (d/y,-x*d/(y * y))))
    
    -- They called this "new" Section 3.2
    constLens :: Num s => a -> Lens s a
    constLens x = Lens (const (x, const 0))
    
    -- or rather we might define add = unlift2 (+)
    instance (Num s, Num a) => Num (Lens s a) where
    	x + y = (lift2 add) (x,y)
    	x - y = (lift2 sub) (x,y)
    	x * y = (lift2 mul) (x,y)
    	abs = error "TODO"
    	fromInteger x = constLens (fromInteger x)
    
    t1 :: Num a => Lens (a,a) a
    t1 = unlift2 $ \(x,y) -> x + y*y + y * 7
    
    -- See section on lifting list functions form biapplicative paper
    -- These are could be Iso.
    lcons :: Lens (a,[a]) [a]
    lcons =  Lens $ \(a,as) -> (a : as, \xs -> (head xs, tail xs))
    lnil :: Lens () [b]
    lnil = Lens $ const ([], const ())
    
    lsequence :: Num s => [Lens s a] -> Lens s [a]
    lsequence [] = lift lnil unit
    lsequence (x : xs) = lift2 lcons (x, lsequence xs)
    
    llift :: Num s => Lens [a] b -> [Lens s a] -> Lens s b
    llift l xs = lift l (lsequence xs)
    
    
    instance (Num a) => Num [a] where
    	(+) = zipWith (+)
    	(*) = zipWith (*)
    	(-) = zipWith (-)
    	abs = map abs
    	fromInteger x = repeat (fromInteger x)
    
    -- We need to hand f a list of the accessor lenses
    -- [Lens [a] a]
    -- This feels quite wrong. Indexing into a list is naughty.
    -- But that is what they do. Shrug.
    lunlift :: Num a => (forall s. Num s => [Lens s a] -> Lens s b) -> Lens [a] b
    lunlift f = Lens $ \xs -> 
    					let n = length xs in
    					let inds = [0 .. n-1] in
    					let ls = map (lproj n) inds in
    					let (Lens f') = f ls in
    					f' xs
    
    t2 :: Num a => Lens [a] a					
    t2 = lunlift sum
    t3 :: Num a => Lens [a] a					
    t3 = lunlift product
    
    lproj :: Num a => Int -> Int -> Lens [a] a
    lproj n' ind = Lens $ \xs -> ((xs !! ind), \x' -> replace ind x' zeros) where
    	replace 0 x (y:ys) = x : ys
    	replace n x (y:ys) = y : (replace (n-1) x ys)
    	zeros = replicate n' 0
    
    	
    lensmap :: Applicative f => Lens a b -> Lens (f a) (f b)
    lensmap (Lens f) = Lens $ \fa ->
    								let fbb = fmap f fa in
    								let fb = fmap fst fbb in
    								let fb2s = fmap snd fbb in
    								(fb, \fb' -> fb2s <*> fb')
    
    -- Types work, but does this actually make sense?
    lsequenceA :: (Applicative f, Applicative t, Traversable f, Traversable t) => Lens (t (f a)) (f (t a))
    lsequenceA = Lens $ \tfa -> (sequenceA tfa, sequenceA)
    
    ltraverse :: (Applicative f, Applicative t, Traversable f, Traversable t) =>
                 Lens a (f b) -> Lens (t a) (f (t b))
    ltraverse f = lsequenceA . (lensmap f)
    
    lensfoldl :: Traversable t => Lens (a, b) a -> Lens (a, t b) a
    lensfoldl (Lens f) = Lens $ \(s, t) -> let (y, tape) = mapAccumL (curry f) s t  in
    						  (y,  \db ->  mapAccumR (\db' f -> (f db')) db tape)
    lensfoldr :: Traversable t => Lens (a, b) a -> Lens (a, t b) a
    lensfoldr (Lens f) = Lens $ \(s, t) -> let (y, tape) = mapAccumR (curry f) s t  in
    						(y,  \db ->  mapAccumL (\db' f -> (f db')) db tape)						  
    
    t5 = grad'' (lensfoldl mul) (1, [1,1,2,3])
    
    
    liftC :: Num a => (Lens a b -> Lens c d) -> (forall s. Num s => Lens s a -> Lens s b) -> (forall t. Num t => Lens t c -> Lens t d)
    liftC c f = lift (c (unlift f))
    
    ungrad :: Lens (a,b) c -> (a -> Lens b c)
    ungrad (Lens f) a = Lens (\b -> let (c,j) = f (a,b) in (c, snd . j))</code>









