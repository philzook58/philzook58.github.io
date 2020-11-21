---
author: philzook58
comments: true
date: 2020-02-07 15:52:53+00:00
layout: post
link: https://www.philipzucker.com/a-sketch-of-gimped-interval-propagation-with-lenses/
slug: a-sketch-of-gimped-interval-propagation-with-lenses
title: A Sketch of Gimped Interval Propagation with Lenses
wordpress_id: 2645
categories:
- Formal Methods
- Haskell
tags:
- interval
- lens
---




David Sanders (who lives in Julia land [https://github.com/JuliaIntervals](https://github.com/JuliaIntervals) ) explained a bit of how interval constraint propagation library worked to me last night. He described it as being very similar to backpropagation, which sets off alarm bells for me. 







Backpropagation can be implemented in a point-free functional style using the lens pattern. [http://www.philipzucker.com/reverse-mode-differentiation-is-kind-of-like-a-lens-ii/](http://www.philipzucker.com/reverse-mode-differentiation-is-kind-of-like-a-lens-ii/) Lenses are generally speaking a natural way to express in a functional style forward-backward pass algorithm that shares information between the two passes .







I also note Conal Elliot explicitly mentions interval computation in his compiling to categories work [http://conal.net/papers/compiling-to-categories/](http://conal.net/papers/compiling-to-categories/)  [https://github.com/conal/concat](https://github.com/conal/concat) and he does have something working there.







Interval arithmetic itself has already been implemented in Haskell in Ed Kmett's interval package. [https://hackage.haskell.org/package/intervals-0.9.1/docs/Numeric-Interval.html](https://hackage.haskell.org/package/intervals-0.9.1/docs/Numeric-Interval.html) so we can just use that.







The interesting thing the backward pass gives you is that everything feels a bit more relational rather than functional. The backward pass allows you to infer new information using constraints given down the line. For example, `fuse :: Lens (a,a) a`  let's you enforce that two variables we actually equal. The lens pattern lets you store the forward pass intervals in a closure, so that you can intersect it with the backwards pass intervals.







I make no guarantees what I have here is right. It's a very rough first pass. It compiles, so that is cool I guess.






```haskell
module Numeric.ADLens.Interval where
import Numeric.Interval

-- interval combinators

type Lens a b = a -> (b, b -> a) 

class Lattice a where
   (/\) :: a -> a -> a
   (\/) :: a -> a -> a
   top :: a
   bottom :: a

-- x /\ x = x
-- 

instance (Lattice a, Lattice b) => Lattice (a,b) where
    (x,y) /\ (a,b) = ( x /\ a  , y /\ b )
    (x,y) \/ (a,b) = ( x \/ a  , y \/ b )
    top = (top, top)
    bottom = (bottom, bottom) -- ? very fishy


instance (Fractional a, Ord a) => Lattice (Interval a) where
    (/\) = intersection
    (\/) = hull
    top = whole
    bottom = empty


instance Lattice () where
    _ /\ _ = ()
    _ \/ _ = ()
    top = () -- fishy
    bottom = () -- fishy



id :: Lattice a =>  Lens a a
id = \x -> (x, \x' -> x  /\  x')
dup :: Lattice a =>  Lens a (a,a)
dup = \x -> ( (x,x), \(x1,x2) ->  x1 /\ x2  )

fuse :: Lattice a => Lens (a,a) a
fuse = \(x,x') -> let x'' = x /\ x' in ( x'' , \x''' -> let x4 = x'' /\ x''' in (x4, x4))  

-- cap is equality
cap :: Lattice a => Lens (a,a) ()
cap = \(x,x') -> ((),  \_ -> let x'' = x /\ x'  in (x'', x''))


posinf :: Fractional a => a
posinf = sup whole
neginf :: Fractional a => a
neginf = inf whole

-- insist that x <= y
leq :: (Ord a, Fractional a) => Lens (Interval a, Interval a) ()
leq = \(x,y) -> (() , \_ ->  (  x /\ (neginf ...  (sup y))  ,  y  /\  ( (inf x) ... posinf) )  )

-- the repetitive-ness of the /\ is a real code smell.
swap :: (Lattice a, Lattice b) => Lens (a,b) (b,a)
swap = \(x,y) -> ( (y,x) , \(y',x') -> (x /\ x', y /\ y' ) )

-- min :: Lens (a,a) a
-- min = \(x,y) -> (min x y, \m -> (x /\ (m + pos)  ,  y /\ (m + pos))

cup :: Lattice a => Lens () (a,a) -- not a very good combinator
cup = \_ -> ( (top, top) ,  \_ -> () )

-- it sure seems like we are doing a lot of unnecessary /\ operations
labsorb :: Lattice a => Lens ((), a) a
labsorb = \(_, x) -> (x, (\x' -> ((), x' /\ x)))
-- rabsorb 

{-
and vice verse

-}



compose f g = \x -> let (y, f' ) =  f x in
                    let (z, g' ) = g y in
                    (z , f' . g')
-- we could do the intersection here.
{-
compose f g = \x -> let (y, f' ) =  f x in
                    let (z, g' ) = g y in
                    (z , \z' -> f' (y /\ (g' z')) /\ x)
                    -}
-- can we though? Does this still work for add?

{-
yeah no, there is something off.
You need to change what you do depending on the number of arguments to the function.
hmm.

-}

const :: a -> Lens () a
const x = \_ -> (x, \_ -> ()) 

{-

Functions and taylor models... ????


-}

fst :: Lattice a => Lens (a,b) a
fst = \(x,y) -> (x, \x' -> (x /\ x', y))
snd :: Lattice b => Lens (a,b) b
snd = \(x,y) -> (y, \y' -> (x, y /\ y'))


-- par :: Lens a b -> Lens c d -> Lens (a,c) (b,d)
-- par f g = 


sum :: (Num a, Lattice a) => Lens (a,a) a
sum = \(x,y) -> ( x + y, \s -> ( x /\ (s - y),  y /\ (s - x)))
mul :: (Fractional a, Lattice a) => Lens (a,a) a
mul = \(x,y) -> (x * y, \m -> (x /\  (m / y)  , y /\ (m / x) ))

div :: (Fractional a, Lattice a) => Lens (a,a) a
div = \(x,y) -> (x / y, \d -> ( (d * y) /\ x ,  ((recip d) * x) /\ y ))

liftunop :: Lattice a => (a -> b) -> (b -> a) -> Lens a b
liftunop f finv = \x -> ( f x , \y -> x /\ (finv y) )

recip' :: (Fractional a, Lattice a) => Lens a a
recip' = liftunop recip recip
sin' :: (Floating a, Lattice a) => Lens a a
sin' = liftunop sin asin
cos' :: (Floating a, Lattice a) => Lens a a
cos' = liftunop cos acos
acos' :: (Floating a, Lattice a) => Lens a a
acos' = liftunop acos cos
exp' :: (Floating a, Lattice a) => Lens a a
exp' = liftunop exp log

-- depending on how library implements sqrt?
sqr :: (Floating a, Lattice a) => Lens a a
sqr = \x -> (x ** 2, \x2 -> x /\ (sqrt x) /\ negate (sqrt x) )

-- sqrt = liftunop ()
pow :: (Floating a, Lattice a) => Lens (a,a) a
pow = \(x,n) -> ( x ** n, \xn -> (x /\ xn ** (recip n),  n /\ (logBase x xn) ))




```






Here's my repo in case I fix more things up and you wanna check it out [https://github.com/philzook58/ad-lens/blob/master/src/Numeric/ADLens/Interval.hs](https://github.com/philzook58/ad-lens/blob/master/src/Numeric/ADLens/Interval.hs)







Now having said that, to my knowledge Propagators are a more appropriate technique for this domain. [https://www.youtube.com/watch?v=s2dknG7KryQ](https://www.youtube.com/watch?v=s2dknG7KryQ) [https://www.youtube.com/watch?v=nY1BCv3xn24](https://www.youtube.com/watch?v=nY1BCv3xn24) I don't really know propagators though. It's on my to do list.







Lens has a couple problems. It is probably doing way more work than it should, and we aren't iterating to a fixed point. 







Maybe an iterated lens would get us closer?






    
    
```

data Lens s t a b = Lens (a -> (b , (b -> (a, Lens s t a b))))
```








This is one way to go about the iterative process of updating a neural network in a functional way by evaluating it over and over and backpropagating. The updated weights will be stored in those closures. It seems kind of nice. It is clearly some relative of Iteratees and streaming libraries like pipes and conduit (which are also a compositional bidirectional programming pattern), the main difference being that it enforces a particular ordering of passes (for better or worse). Also I haven't put in any monadic effects, which is to some degree the point of those libraries, but also extremely conceptually clouding to what is going on.  








Another interesting possiblity is the type 







type Lens s t a b = s -> (a, b -> t)







Lens s (Interval s) a (Interval a)







This has pieces that might be helpful for talking about continuous functions in a constructive way. It has the forward definition of the function, and then the inverse image of intervals. The inverse image function depends on the original evaluation point? Does this actually make sense?  The definition of continuity is that this inverse image function must make arbitrarily small image intervals as you give it smaller and smaller range intervals. Continuity is compositional and plays nice with many arithmetic and structural combinators. So maybe something like this might be a nice abstraction for proof carrying continuous functions in Coq or Agda? Pure conjecture. 



