---
author: philzook58
comments: true
date: 2017-12-11 16:54:41+00:00
layout: post
link: https://www.philipzucker.com/?p=938
published: false
slug: Fancy Continuation Passing Style in Haskell
title: Fancy Continuation Passing Style in Haskell
wordpress_id: 938
---

There are a number of scary advanced topics related to continuation passing style (CPS). CPS is some sort of mental nexus for interesting shit to happen.

CPS gives you a thing with a name that says where you are going next.

Simple CPS is a way to make an isomorphism between values and functions. Basically the body of that function only consists of the value.

it looks like this

4     <=>    (\f -> f 4)

In terms of types the correspondence is

a      <=>   forall b. (a -> b) -> b

The forward transformation is given by

cpsify x = \f -> f x

or in terse cryptic Haskell

cpsify = flip ($)

The reverse transformation is given by

uncps = id

You can see this by

(cpsify x) uncpsify = (\f -> f x) id = id x = x



The CPS transform is associated with tail-call optimization. Tail calls, where the last thing a function does is to return the result of another function, can be optimized away. You don't need to return to the current context, you just need to tell the tail called function to pass it's result to the original caller. Therefore, you don't need to store a huge stack or traverse back up the stack. You pass down into the next guy the place he needs to return his results to .

One way, we can generalize CPS by considering generalization of function application. If you squint your eyes fmap is kind of a generalized function application, so is monadic bind. You could imagine calling the continuation by using  'fmap cont res' rather than just 'cont res'

cpsify is the return of the continuation monad.

The ContT monad transformer builds a new monad where function application is replaced with bind?



Hughes Lists are lists converted to a continuation style function using append.

There is a cute little trick that sometimes it is useful for generalization purposes to add the Identity functor (which does basically nothing) to the types, then see what you get when you replace Identity with more general functors or require it to be a monad. Maybe you get something interesting. The trick is especially important when you have an unwrapped polymorphic type like b above. The forall b. may or may not be explicitly written, but is always at least implicitly there.

forall b. (a -> b) -> Identity b

forall b. (a -> Identity b) -> Identity b

The generalization of this might be

Functor f => forall b. (a -> b) -> f b

Monad f => forall b. (a -> f b) -> f b

The first is sometimes referred to as the Yoneda Lemma. fmap is kind of like a fancier ($). A function of this type is isomorphic to (f a).

Monadic bind >>= is also like a fancier function application ($). The Codensity Transformation is an advanced topic.



Just as an aside, another interesting topic related to CPS is the embedding of classical logic into intuitionistic logic. Call/cc. Call/cc is call-with-current-continuation. It's kind of a confusing operator. I don't believe that it is implemented in terms of more familiar constructs, it is a fundamental power to give your language. Call/cc grabs up the entire current universe and constructs behind the scenes a continuation f. It is sometimes described as an escape hatch.

A third topic is the Continuation Monad as the mother of all monads.




