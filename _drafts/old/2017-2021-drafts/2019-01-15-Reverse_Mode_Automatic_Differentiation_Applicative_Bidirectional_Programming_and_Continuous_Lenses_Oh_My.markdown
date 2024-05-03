---
author: philzook58
comments: true
date: 2019-01-15 20:53:04+00:00
layout: post
link: https://www.philipzucker.com/?p=1640
published: false
slug: Reverse Mode Automatic Differentiation, Applicative Bidirectional Programming,
  and Continuous Lenses. Oh My.
title: Reverse Mode Automatic Differentiation, Applicative Bidirectional Programming,
  and Continuous Lenses. Oh My.
wordpress_id: 1640
---

The king of automatic differentiation is Ed kmett's ad package. If you want to do some automatic differentiation, look there. But let's have some fun anyhow

In a previous post, I showed how you can build a DSL for reverse mode automatic differentiation.

/u/syrak posted an interesting link to a recent paper by Kazutaka Matsuda and Meng Wang called "Applicative Bidirectional Programming"

The CPS trick. forall b. ( Int ->b )->b   ~  Int. And Int doesn't matter.

The Yoneda1 trick. forall b. (Int -> b) -> f b ~ f Int

Using f = Reader String

forall b. (Int -> b) -> (String -> b)   ~    String -> Int

You can flip stuff around

They Yoneda-fy Lens.

forall s t. Lens s t a b -> Lens s t a b

It is useful to turn a -> n into a Num if n is a Num, although frowned upon.

They are targetting lenses specifically, so they go through a great deal of trouble of explaining how you can make a sensible dup for lenses.

type L s a = PoSet s => Lens s a

We already had one naturally though. Instead we made s a Num. In particular, we need it to have addition, because that is how.

They make values into Posets by giving them Tags. We can also do something useful with a Zero tag.  There was some amount of unnecessary zero addition occuring from stuff like fst.

fromInteger 0 = Nothing/Zero

forall s. Lens s a is something like the value a itself.

instance (Num s, Num a) => Num (Lens s a) where

In my first post, I had made the mysterious to myself note that the derivative in a sense is a value that tells you how to update stuff.

The derivative gives you local information about how to update the input to make the output some value. It turns differential updates of the output into differential updates of the input... Is that right. The derivative turns differential updates of the input into differential updates of the output. Then some kind of pseudo inverse procedure (Newton Step) might got the other way

The composition laws for Hessians are more annoying but doable. Is there a reasonable definition of reverse mode for higher order derivatives? I've tried stuff, but it has felt clunky. Mainly the indices of the Hessian, some are covariant and some contravariant.

But what if we take the update form literally. An invertible function has functions a -> b, b -> a. It is an isomorphism.

A quasi invertible, or locally invertible function. a -> b, a -> b -> a. We need to know the initial position in order to know which solution of the backward equation to pick.

Now, there is a reasonable general purpose method that work's pretty well. Newton's method. But in general, I don't need to specify how it works or what the local regions of convergence are. They are still compositional.

We want to measure. We want kind of the proximal problem.   min dx dxHdx, s.t. f(x+dx)=y. This is only a convex problem if f is linear. We could use a global solver.

Lens are bidirectional. So are relations. So Lens may be a better building block for deductive relational reasoning than functions are.

A two way lens (a -> b -> a) (b -> a -> b). Pseudo inverse in both directions.

Duality. Linear functional on  (x -> f -> x)

Monotonic functions. (x -> f -> x) . Are isomorphisms.

f x + lam x. Addition. (x -> (f, (x -> f) -> f)

(x -> f, (x -> f) -> x). A function plus a mapping from linear functionals to values. min x lambda(x) + f(x).  (x -> y, Dual x -> x)

(x -> f)

fix (Lens s a)

Projection.

Projections are the pseduo inverse of set detection x -> (Bool, Bool -> x)

The dup function will require compromise. What happens when two conditions conflict? BiApp paper worries about this significantly with the tagging system. Our tags will be... derivatives?

Forward function, and then the backward function is an ad function.

x -> (y, ADLens y x)

Categorical compositon. x -> (y, k y x) is what Conal Elliott talks about in his AD paper. I guess there is a functor? that loses.. the outer stuff?

How do we handle asking for an output value that can't be had. I guess the backwards direction is also a projection?

The recrusive type.

data PseudoInv = P (x -> (y, PseudoInt y x))

Then The input is actually (x, Bool) -> (y, Bool)

first bool is if y is in the domain, scond bool is if x is in the domain. The pseudoInverse of -inifty might be the minimum. We need to fix out the bools.

data Set = (x -> (Bool, Bool -> x) .. Is refactorable a number of ways. But it packs together a indicator and projector function. There is a category here. we have composition and identity...?

Convex cones generalized inequalities are a binary operator that becomes

(x,y) -> Bool. It is the same thing as y -x being in K. which is a set op (<=K) = inK . subC

hmm Proximal operators and subgradients. I hadn't yet considered those really. Subgradient is the set of all underlying derivatives.

What is Min? Requires derivatives too? Requires duality realized (dual certificates)?
