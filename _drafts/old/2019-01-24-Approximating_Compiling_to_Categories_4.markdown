---
author: philzook58
comments: true
date: 2019-01-24 19:16:16+00:00
layout: post
link: https://www.philipzucker.com/?p=1623
published: false
slug: 'Approximating Compiling to Categories 4:'
title: 'Approximating Compiling to Categories 4:'
wordpress_id: 1623
---

I was hoping the closed instances wouldn't be that much worse than the cartesian instances. There are some hiccups.

The strategy is to curry the function as much as possible. We also fan the output as much as possible, until the output is simple.

If the function takes a function as input, that requires a special case for BuildInput. When that function is used, it is a use of applyC.

Unfortunately, by placing a morphism into the input of a function, we are specializing that type variable. During the fanning process of the output, we'd like to specialize the input to different things that might show up.

I haven't found a way out of this yet.

So the implementation works sometimes. For straightforwardly curried functions, it is fine. For some higher order functions, it is fine. but stuff like (\x -> (x, \y - >y)) it is not fine.

We might as well, go back to the simpler architecture. Autocurry, then buildInput with the new higher order bit, then FanOutput.

I see the roadblock, but it is not clear that there isn't some way around it altough my 3 or 4 different attempts have been stymied so far.

We can only apply the function to input usefully once. In the other cases the types don't work out.

What if we boxed up the controlling types with a GADT?

UseThis :: a  ->  Proxy 'True -> Var a b

NotThis :: a ->  Proxy 'False -> Var a b

Ok. One workaround that seems rather odd. We can make a Either Tree that matches the sturcture of fanning. We pass down the Left Right sequence as we fan. Then we need to reverse it and pass it unadultered until we really are builing the input to the function. At that point, we can inject into the Either Tree. injecting and extracting using the same Right Left path sequence is safe, even though it is partial.In this way, we get something down at the leaves of the input tuples that works for the different fan cases.

This is very very very roundabout.

In addition, I wrote a simple rewrite program, mostly just so I could see the cleanedup FreeCat output.

How to optimize?

1. rewrite rule strategy. Come up with rewrite rules and analyze them for confluence or termination

2. Brute force. Enumerate All possible trees. Use equivalency check to simplest tree/ use rewrite rules already found to try and make it easier. Equivalency check for rewriting functions can be found by applying them once. This is also, amusingly, a toCCC strategy. We could apply the original function once, then compare the output to the intepretted CCC functions.

We can use Z3 to evaluate the equivalency of two catgeories raw dog. Z3 will be able to handle addition and times, And and Or. Then ask for counterexamples. Super-compiling categories. If we could prune the space of Cat ASTs, that'd be nice. Only ask for ones with the right type.

We can also use Z3 with holes? Enumerate 1 hole, 2 hole, 3 hole programs.

So a multi stage strategy. Try to apply simple rules first. Then brute force on subtrees? Try to recocgnize common subxpressions

The Functor between Hask and whatever category is Monoidal. It respects the monoidal structure/ The Applicative typeclass is also known as monoidal. Could we make (k z) an applicative functor and somehow

fmap :: (a -> b) -> (k z) a -> k z b

fmap f x = (toCCC f) . x

<*> ::  k z (a -> b) -> k z a -> k z b

<*> f x = applyC . (parC (fmap toCCC f) x)

pure :: a -> k z a

pure = constC  --- Const :: b -> FreeCat a b

idlift :: b -> k b b

idLift = idC

idUnlift :: k b b -> b ?

liftA

liftA2

If you program in applicative style, you might get more control over the toCCC process.

Applicative Functors compose. We can compose Categories with Functors in the output

FunctorCat k

fmapC :: k b c -> k a (f b) -> k a (f c)

Arrow. WrappedArrow is in applicative.

So one might try to write an autolift using my techinques. Since applicatvie functors are monoidal functors.

autolift :: Applicative f => (a -> b) -> (f c -> f d)

Then using the cayley cps thing (preapplying compose

(forall s Cat s a -> Cat s b)  we might be able to match this with autolift. Will the forall s. be a problem?
