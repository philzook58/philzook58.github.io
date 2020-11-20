---
author: philzook58
comments: true
date: 2016-08-28 22:32:53+00:00
layout: post
link: https://www.philipzucker.com/haskell-where-am-i-at/
slug: haskell-where-am-i-at
title: Haskell - Where am I at?
wordpress_id: 496
---

A long list of scattered thoughts. I need more examples.

Functors:

fmap generalizes map on lists. If you can apply a function and inject it into a container it is a functor.

Examples: trees. Simple wrappers. Records.

Alternatively Functors are category theory functors. The combo of the type constructor (Which maps a into Constructor a) and fmap (which maps the morphisms)

Foldable:

foldMap is like concatMap.

I am confused.

Traversable:

traverse is like fmap except "effectful"?

traverse is like mapM for applicatives? Like a mapA. mapM is like map except it uses bind instead of apply. So if you had a list of Maybe Ints you could mapM over them to apply a monadically defined function Int -> mb to all elements. So instead you use <*> I guess? If you had a...

sequence is like? It flips outside and inside wrappers? List of Maybes to a Maybe List. Like transposing a matrix ? Hmm. The matrix is a bit confusing because there is a traversable and an applicative at play

I am confused.

Applicative:

slightly less powerful monads. Equal to do notation if you don't use values until the return.

Applying a list of functions to a list of arguments. Either zipwise or nondeterministic/cartesian product wise.

If you fmap <$> a multiargument function over a list you get a list of functions via currying.

(+) <$> [1,2] <*> [7,8]

will return a list of all possible sum combos via the default applicative list instance.

I am pretty darn confused about applicative. I don't have examples of applicatives that aren't also monads although I've seen the claim there are many.

Lens:

Look at Simon Peyton Jones talk. It helped a lot. Ed Khmett's talk is very puzzling from the get go. It assumes comfort levels with traversable and foldable.

Lens a b are kind of functiony "things" that have a big object a and a focus within that object b.

Simplest lens would be a hand written setter and getter functions

something like the _1 lens would look like

_1  {get = \(x,y) -> x, set a = \(_,y)->(a,y)}

Composable. Sort of compose setters and getters if one guy is inside of another. I think there is some pipework for getting set to work.

Can be unified into a single interface. Lens' which uses Functorial trickery. Using trivial seeming Functors can be useful. Identity and Const.

Interesting connection between type level and value level.

fix, id, const and Fix Identity and Const

Recursion Schemes:

[http://blog.sumtypeofway.com/an-introduction-to-recursion-schemes/](http://blog.sumtypeofway.com/an-introduction-to-recursion-schemes/)

Nutso shit.

Maybe a start is to try to right fold in terms of fix. Don't use recursion except fix

Bananas Barbed Wire territory. Paper is incomprehensible due to using Squiggol notation

fix f = let x= fx in x

let is a primitive construct of its own.

bottom is the value a function returns when it gets into an infinite loop (If we insist on things being for real mathematical functions that have to return). bottom is always a possible value. You can't really return bottom in some sense because of the Halting problem being unable to determine if stuff will halt (although in special cases its possible btw).

[https://en.wikibooks.org/wiki/Haskell/Denotational_semantics](https://en.wikibooks.org/wiki/Haskell/Denotational_semantics)

Profunctors:

Seem really important. This is the most promising area for me to find a good approach to anyon models.

Contravariant Functors are functors where fmap kind of reverse what happens.

There is a related funniness where you would apply f then apply g but the composition is written g . f  The order is swapped in some kind of wonky way between application and composition

Wrapping Isomorphisms as type. The Product type of the map and inverse map of the isomorphism.

Monads:

Labelled arrows that aren't quite functions. Partial functions, Linear functions, Nondeterministic functions, random functions, state dependent functions.

bind is an awful lot like function application $.

Useful technique: Dumb write all the stuff you need to pass around, then try and push it all onto the right hand side. state dumbly = s -> a -> (s' , b) . Returns new state s' and result b when given original state s and argument a.

DRYing up function pipework (always error checking in every function).

It might tend to be better to understand and use monads without delving into their definition. They form their own language. (DSL) Undoing do notation in your head is a nightmare

CoMonad:

contextual arrow instead of effectful arrow

duplicate instead of join

Monad Transformers:

Stacking monads. That's all I got.










