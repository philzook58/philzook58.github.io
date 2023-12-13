---
author: philzook58
comments: true
date: 2018-08-03 14:58:38+00:00
layout: post
link: https://www.philipzucker.com/?p=929
published: false
slug: Kan Extensions
title: Kan Extensions
wordpress_id: 929
---

The Right Kan extension theorem is a fairly simple Haskell statement

forall a. h (f a) -> g a  ~=  forall b c. h b -> (b -> f c) -> g c

Just a curious theorem.You can find the implementation of the isomorphism by following the smell of the polymorphic types

In a sense, this is "currying" of functor composition

compare to

(a,b) -> c ~= a -> b -> c

We replace a compound object with something that can be partially applied



Polymorphic values are opaque pointers. The type system does not let you dereference them, The way you can dereference them is to have an explicit function type (a -> whatever). Having that around tells us a is a reference to the whatever. Putting type class restrictions on a tells us what the data underlying the pointer implements.



Kan Extensions themselves are sort of a way to "invert" a functor in a certain use context.

$latex I/F \circdot F ~ Id $ Is the formula that describes how I/F is the adjoint of F. (I need to actually check the ordering of this stuff. One point of complexity is that adjoints aren't actually inverse functors, they are something close. That is why the right and left kan extensions are used to give the left and right adjoints)

$F/Id ~ F$ This is basically the Yoneda lemma.

forall b. (a -> Id b) -> f b ~ f a

The codensity moand $latex F/F$ has the property of 1 that you can multiply 1 * 1 * 1 *1 ... = 1. Similarly you can collapse many applications of F/F into a single application of F/F.





Consider the natural transformation $latex Maybe V2 a -> [a] $ The obvious implementation is Nothing -> []

and Just V2 x y -> [x,y] although there are others (permuting, duplicating, dropping elements of V2).

There is a direct implementation in the Kan form

ex :: Maybe b -> (b -> V2 a) -> [a]

ex Nothing _ = []

ex (Just x) f =   [y,z] where V2 y z = f x

I think actually this form shows more clearly that Nothing had to go to [].

What the hell is x in this context? We can never know. But x was kind of a pointer to the appropriate V2 instance that we dereference by applying f.

ex (Just pointer) star =   [y,z] where V2 y z = star pointer

V3 (V2 a) -> V4 a

(V3 a) -> (a -> V2 b) -> V4 b



Really it fells more like the point is

f g a ~ forall b. (f b, (b -> g a))



Is the efficiency thing come in if we want to do stuff on V2, but we don't want to fmap inside a deep structure that mayb be V3 every time?

Is there some possible benefit to sharing here?

fmap (a -> b) :: f g a -> f g b

fmaps destroy sharing.

A model of sharing: two composed functors, but the inner one is shared at multiple spots of the outer one. You can do this with a let expression. But then as soon as you fmap, typically it smashes the sharing apart (I think. To notice the sharing is too magical in general).



https://bartoszmilewski.com/2017/04/17/kan-extensions/

The Kan Extension is a way to extend a functor to a new domain. You could extend a functor by some other random functor. That is the analog of a cone. But then the Best Functor is the one where all the others have a Nat trans to or from it. That is the difference between a cone and a limit.

In terms of Set, maybe one Set is a subset of the other. Then the functor could be just inclusion. Is this a kan extension though?



If one of the categories is the 1 category, the Kan extension becomes limits and colimits.

In some sense, Kan extension is inverse of functor composition(kind of multiplcaltion).



Right Kan extensions packs together a natural transformation and a value

    
    newtype Ran k d a = Ran (forall i. (a -> k i) -> d i)




the Free Functor

    
    data FreeF f a = forall i. FMap (i -> a) (f i)






Hom( F.J , G ) ~ Hom(F,G/J) that is natural in F. Functor category where Functors are objects and natural transformations are morphism

is reminscent of describing adjunctions as Hom(F a, b) ~ Hom(a, G b)

Instantiating F to different things gives us other stuff

Instantiating b to be a inlcudes id in the Homset.
