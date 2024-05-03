---
author: philzook58
comments: true
date: 2020-11-09 23:48:55+00:00
layout: post
link: https://www.philipzucker.com/?p=2689
published: false
slug: Coroutines / Iteratees / Stream Transformers
title: Coroutines / Iteratees / Stream Transformers
wordpress_id: 2689
---

https://news.ycombinator.com/item?id=25218601 - Existential types y combinator post

Lists are one of the most common and useful data structures in programming.

A fundamental programming concept 

Terminology and implementation varies between languages. Some call things sequences, lists, streams, vectors,  generators, iterators.

Some of these things are data structures, but some are data and control structures. These control structures are functions associated with the data type, perhaps as object methods, or perhaps as attached functions

Some of the basic functions

  * List consumers. sum, product, head
  * List producers, repeat, list constants
  * List transformers, tail

What is the difference between streams and lists. 

Streams are ephemeral. They are the capacity to produce elements, not necessarily data in memory.

There is a class of complicated seeming abstractions whose purpose

There are two major persepctives on this

  * A reshuffling of the type of list function
  * As a little DSL for describing machines or in some sense the machines themselves

iterators are very similar to streams.

### Lists and consuming Lists and consuming consumers of lists

There are two things we want to talk about, streams and lists

A method I like to use for discovery is free association on types. I write down a type, and just think about what kinds of types are equivalent, or merely similar in some vague sense.

    
    <code>[a]
    [a] -> b
    
    -- effectful
    m [a]
    [m a]
    m [a] -> d
    [m a] -> d
    
    data MList m a = Nil | Cons a (m (MList m a))
    
    </code>

First let's look at the simplest versions of these things. Data sources are streams and lists. Lists have the ability to say "I'm empty" with a []. Streams aren't allowed to ever stop, the poor fellows.

    
    <code>data Stream a = Next a (Stream a)
    type List a = [a]</code>

A list consumer is a function. Maybe this takes the head of the list. Maybe this sums up the list. These things are sometimes called iteratees.

    
    <code>type ConsumeL a b = [a] -> b
    type ConsumeS a b = Stream a -> b</code>

A stream transformer is a function that takes in a stream and outputs a stream

    
    <code>type TransformerL a b = [a] -> [b]
    type TransformerS a b = Stream a -> Stream b</code>

Very good. Now we can start to play games. 

One thing we can note is that

    
    <code>Consumer a [b] = Transformer a b</code>

Another thing we can note is

    
    <code>[a] -> [b] ~ forall s. (s -> [a]) -> (s -> [b]) -- yoneda embed1
    [a] -> [b] ~ forall s. ([b] -> s) -> ([a] -> s) -- yoneda embed2
    [a] ~ ([a] -> s) -> s -- cps</code>

    
    <code>data Iteratee a b = Await (a -> Iteratee a b) | Done b
    ~ Stream a -> b
    
    data IteratteeEOF a b = Await b (a -> IterateeEOF a b) | Done b
    ~ [a] -> b
    
    
    [a] ~ Either (a, [a]) ()
    [a] -> b  ~
    Either (a, [a]) () -> b ==> -- this step is not an isomorphism, instead it changes the function from push to pull
    Either ((a, [a]) -> b) (() -> b) ~
    Either ((a, [a]) -> b) b ~
    Either (a -> [a] -> b) b  ~
    Either (a -> ([a] -> b)) b 
    
    
    forall b. Iteratee a b -> b -- is a cps. this produces a.
    
    
    data Trans a b = Await (a -> Trans a b) | Yield b (Trans a b) | Done
    ~ Stream a -> [b]
    
    data Trans2 a b = Await b (a -> Trans a b) | Yield b (Trans2 a b)
    
    -- these are unknown patterns of communication
    </code>

These are dead values until you interpret them. The [a] -> b machine feels more self running.

Backwards information. You don't magically get backwards flow out of functions. Functions are one way. However, if you're willing to build your primitives with known opposite directions, that's fine.

    
    <code>data Iso a b = Iso {to :: a -> b, from :: b -> a}
    data IsoL a b = IsoL {to :: [a] -> [b], from :: [b] -> [a]}
    IsoL a b ~ Iso [a] [b]
    
    type Iso a b = (a -> b, b -> a)
    type Lens a b = a -> (b, b -> a)
    
    data IterLens a b = (a -> (b, IterLens b a)
    </code>

    
    <code>[a] -> [b]</code>

Pushing versus pulling. In the first function, the supplier of the value gets to pick either an `a` or a `b`. In the second, the supplied of the function gets to pull whether it gets an a or b. In the second, the supplied needs to have both (a,b) just in case. In the first, the supplier only needs to have one.

I'm not convinced push pull is the best way to think about this. It's also, which one has the action in it, the pattern match. Push and pull often feel like suppliers and consumers, contravariant vs covaraint

    
    <code>Either a b -> c  -- c ^ (a + b)
    not equiv to
    Either (a -> c) (b -> c) -- (c ^ a + c ^ b)</code>

Consider Bool -> b versus (Either b b). Clearly one accepts choices and the other produces a choice. So it really is a contravariant vs covariant issue. Do the choices lie in the contravariant or covariatns part. It's hard to see when list has 

    
    <code>data Nat = Succ Nat | Zero -- "list"
    data Tramp = Jump Tramp -- "stream"
    
    Nat -> b vs   [b] ?</code>

The canonical push pull is functional rpgramming is contravaraitn vs covaraint position in a type. 

The next thing that comes up is Lazy vs strict.

Data and pattern match. Data is inert, pattern matches to stuff. And yet the too are equivalent in some respects.

Dialogical logic. Lens. Dialectica

Existentials and 

The difference between Algebra and Coalgebra is obscured by the fact that you can kind of use Haskell

[https://github.com/BartoszMilewski/Publications/blob/master/Algebras.pdf](https://github.com/BartoszMilewski/Publications/blob/master/Algebras.pdf)

    
    <code>data Fix f = Roll (f (Fix f)) -- standard Haskell Fix definition
    newtype Mu f = Mu (forall s. (f s -> s) -> s)
    data Nu f where
      Nu :: !s -> (s -> f s) -> Nu f 
    
    
    data ListF a s = Nil | Cons a s
    type List a = Mu (ListF a)
    type CoList a = Nu (ListF a)
    
    -- this one allows state.
    data Nu f where
       Nu :: ST s b -> (b -> ST s (Nu f)) -> Nu f
    
    data Iteratee a = More (a -> 
    </code>

[https://yanniss.github.io/streams-popl17.pdf](https://yanniss.github.io/streams-popl17.pdf) Stream fusion to completeness

[https://stackoverflow.com/questions/292274/what-is-an-existential-type](https://stackoverflow.com/questions/292274/what-is-an-existential-type)

[https://wiki.haskell.org/Existential_type](https://wiki.haskell.org/Existential_type)

[https://link.springer.com/chapter/10.1007/978-3-030-17184-1_5](https://link.springer.com/chapter/10.1007/978-3-030-17184-1_5)

Existentials have some relation with objects. The

Existential |-   weakening  |- universal. 

data and codata

colist seems very similar to rust iteratees. There is this state that you can't see because it is hidden behind a trait. You carry it along and get a Some or None.

It has the flavor of the coyoneda. If you existentialize and you have some functions that take it, the only thing you can do

If alternate forms of Fix can include sharing and unification, is there something interesting to say about CoFix?

[https://arxiv.org/pdf/1907.13227.pdf](https://arxiv.org/pdf/1907.13227.pdf) compiling with connectives

The story behind these things is rather confusing, but made worse by including unessential pieces.

I

