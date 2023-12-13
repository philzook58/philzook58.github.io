---
author: philzook58
comments: true
date: 2018-03-06 22:42:34+00:00
layout: post
link: https://www.philipzucker.com/?p=1006
published: false
slug: Purescript GADTS
title: Purescript GADTS
wordpress_id: 1006
---

I had peeked at these aryicles months ago and just thought they looked too complicated. T

https://www.cs.ox.ac.uk/files/3060/gadtless.pdf

https://futurice.com/blog/more-gadts-in-purescript

His Exists  type is directly the Yoneda lemma.

http://code.slipthrough.net/2016/08/10/approximating-gadts-in-purescript/

https://github.com/paf31/purescript-leibniz

https://github.com/garyb/purescript-leibniz-proof

https://github.com/purescript/purescript-exists

What is

The Leibnitz type is similar to what is described as a Toy optic here

https://www.youtube.com/watch?v=l1FCXUi6Vlw

Using Yoneda

forall f. (g ~>f) -> (h ~> f) is the same as (h~>g)

specialziing h = a ->

and g = b ->

Then we have

forall x. (a-> x) -> (b -> x)



lebinitz is forall f. f a -> f b

we can specialize forall f to forall x. (x -> a) -> (x -> b)

which by yoneda gives us a -> b. Kind of. We don't have a Functor instance? No we do, because we're allowed to choose f that have functor instances, which arrow does indeed have.

The contravaraint functor   f = _ -> x

gives us the other way.

So this type minimally has (a -> b, b -> a)

But we want to prove that a really is b. I don't see how. Is this a Free Theorem thing?



There is the secondary question of what if one replaced the leibnitz in GADTless style with something weaker, say an Iso'. This has the feel of saying I want to recplace strict equality of types with isomorphism, which has some of the flavor of HOTT. However, I believe Iso' is not restricted to be an actual isomorphism by naturality.

If such a type  had been found, I would think that someone would have mentioned it.
