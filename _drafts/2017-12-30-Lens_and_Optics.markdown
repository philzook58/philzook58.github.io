---
author: philzook58
comments: true
date: 2017-12-30 22:22:34+00:00
layout: post
link: https://www.philipzucker.com/?p=957
published: false
slug: Lens and Optics
title: Lens and Optics
wordpress_id: 957
---

It feels like there is activity in the lens space. Also, I have been using lens in the Thermite library in purescript and having kind of a hard time. So I dove in for a second look at them.

The Lens library. https://hackage.haskell.org/package/lens

getters and setters are functions. A getter and a setter are individually composable, but you need to perform the composition independently which is inelegant.

It just so happens that there is an interesting trick that makes them composable.

Simon Peyton Jones' explanation really helped me.



The trick does indeed appear to rely on the clever type of Lens being universally quantified in the functor f. Then you can pick some of the trivial functors like Identity or Const and get out setters and getters.

traverse is the same thing as exists. n (A^n, B^n -> t). Traversable functors really do just hold multiple copies of the thing.

Traversable is a very confusing typeclass. Traversable is the main example  of a typeclass that is universally quantified over another functorish object

traverse :: [Applicative](https://hackage.haskell.org/package/base-4.10.1.0/docs/Control-Applicative.html#t:Applicative) f => (a -> f b) -> t a -> f (t b)



https://skillsmatter.com/skillscasts/4251-lenses-compositional-data-access-and-manipulation

Ed Kmett's tutorial video. Pretty Cryptic.

https://www.youtube.com/watch?v=cefnmjtAolY&list;=RDcefnmjtAolY

https://www.youtube.com/watch?v=QZy4Yml3LTY&t;=2555s

https://www.youtube.com/watch?v=l1FCXUi6Vlw

https://www.youtube.com/watch?v=sfWzUMViP0M

Like how lens are setters and getters, prisms are matchers and builders. They let you match on optional structure inside.

If you were looking for some particular pattern and you wanted to keep trying them .

Building a rule based mathematica style thing with prisms.



The Yoneda lemma says that (a -> b) -> f b ~ f a. It is a continuation style transformation of fmap. The Yoneda Lemma is at least one way in which to prove the intuition of "wait, how the hell am I going to get a b. The only thing I can do is use the supplied function" kind of thinking.

Translating to categories, a->b == Hom(a,b), forall x. f x -> g x is a natural transformation. alpha_b :: Hom(a, -) ->  F -

COnsidered as a functor in a, there are two natural transformations from

Yoneda Embedding is

(a->b) -> (c -> b) ~ c -> a



Yoneda Lemma says in category terms that



Bartosz's example of a Toy Optic: forall f. f a -> f s ~ (a -> s)

That makes sense. you only have fmap to deal with the f. So basically this thing was made with fmap h for some h :: a->s. It is interesting very similar to the other yoneda example which used flip fmap instead. He had to go to the functor category and push down with yoneda to get there.

ProYoneda is saying we already partially applied dimap.

dimap _ _ p

and this CPS style thing is equivalent to p itself. we can pass it two id to get back p.

forall p. p s t -> p a b is the same as two morphisms (s -> a, b -> t) which might be getters and setters. This is Iso. Very similar to the shown forall f a -> f b. Again partially applied dimap but in the function arguments now.

The inverse transformation requires more thought though.

forall f. f a -> f b needs to be handed a functor. id is a reader functor.

in the profunctor case though you need a wrapper around it since it hold 2 functions. And then you need to declare a profunctor instance for this wrapped thing



When you add in Strong and Choice and stuff to get Prisms and Lens,

CoYoneda Lemma - exists x. (f x, x -> a ) ~ f a

The only thing you can do is fmap over it. Pretty similar



Russell O'Connor on Comonad Coalgebra

https://arxiv.org/abs/1103.2841v1



forall f. f a -> f b ~ a -> b

forall p . p s t -> p a b  ~ (s -> b , a -> t )

Traversables are finitary containers.
