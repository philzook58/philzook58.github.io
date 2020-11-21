---
author: philzook58
comments: true
date: 2019-04-24 19:52:37+00:00
layout: post
link: https://www.philipzucker.com/?p=1950
published: false
slug: A Roadmap of Reflection
title: A Roadmap of Reflection
wordpress_id: 1950
---




There are a number of disconnected systems in Haskell. Over the years, techniques and extensions have weakened the barriers







  * Values
  * Types
  * Kinds
  * Typeclasses
  * Template Haskell
  * Rewrite Rules
  * Core
  * STG?
  * Liquid Haskell






I think this runs the gamut?







DSLs (Initial, Finally tagless), Generics, Typeable







Is Template Haskell a technique for reflection or a new domain? It is a little fuzzy.







A common thread is that sometimes you have to boiler plate copies of structures in the different domains, and then there is a mechanism to connect the two.







One can create one type definition for every constructor







data Tree = Node Tree Tree | Leaf







data Node a b







data Leaf







The types are much less constrained in this form







The DataKinds extension avoids the need to boiler plate type creation and also creates new kinds such that 







Can I manually create a new kind?  








[http://hackage.haskell.org/package/reflection-2.1.4](http://hackage.haskell.org/package/reflection-2.1.4)







The reflection library connects values -> types via typeclasses. The reify function does this using the "rank-2 ST trick". It is a crazy clever trick that has inspired other weird applications. Why the weird trick? The IO monad cannot be safely escaped. Once you're in IO, you're in IO. The point of ST is that once you're done mutating, maybe you want to freeze the variables and escape ST. You don't want any dangling references then that you can still modify though. So you only want to allow the escape of pure values, not shared modifiable values. So how do you design the escape function?







runST1 :: ST a -> a -- no good.







runST2 :: ST s a -> a -- no good







runST :: (Escapable a) => ST a -> a  -- probably acceptable, but requires boiler plate instances of Escapable. Weird one-off typeclasses like this are kludge that are gonna make everything gunky 







runST3 :: (forall s. ST s a) -> a 







Then mutable references have a tag that references the same scope. binding the two together. What happens if you try to runST






    
    <code>runST (readSTRef (runST (newSTRef 0))) -- shouldn't type check.</code>







The type variable s represents a scope / region of memory. This is very strange and abstract. There is something that tastes similar in Rust with the lifetime system. Lifetimes are type variables representing the (you guessed it) lifetime of that data. When things get cleaned up are described by a theory with a partial ordering. and not much else.







There is scope at the type level (inside forall binders) and scope at the value level (inside lambda binders). The rank2 trick let's us safely reflect the two into each other. RankNTypes lets us have interesting type level scope. (forall a. (a ~ b) => a) -> b. (a ~ ?) is kind of like a typelevel application of the forall typelevel lambda. I can't reuse anonymous functions enough? Once I apply them they're used up?







You can encode an exists using a forall. If I'm capable of doing r if you gave me any x, and I can do that r , then it must mean you gave me some x. (forall x. x -> r) -> r. is the same as there must have been some x. The way I can get that x out is to hand in `id`. I think I am rather annoyed Haskell doesn't have syntax for exists. (forall x. x -> r) -> r is a Church-like form of the datatype exists x. We don't make you use (a -> r) -> r -> r for Maybe a now do we?







When you use reify, you want to ensure that you don't accidentally give it a function that insists on a different type than the one implied by the value, although I suppose this should just result in a type error in the incorrect cases?







Typeclasses are an intrinsic mechanism to turn types to values. Typeclass definitions allows you to connect values/funcitions to types. It's what they do.






    
    <code>
    instance Reifies (Node a b) Tree where
       reflect = Node reflect reflect
    
    instance Reifies (Leaf) Tree where
      reflect = Leaf
    </code>







The actual library uses tricks to avoid this manual boiler plating so that you don't have to write these instances and there isn't an actual type layer connecting the values. You may choose to write them if you'd like (at the expense of performance. It think it is likely that the runtime will shred data apart just to rebuild it. ).







A very similar copying mechanism is used by singletons. The singleton type is a value that has an exact reflection of it's value in it's type. There are very boilerplaty singletonizing functions






    
    <code>snat :: Nat -> (forall s. SNat s -> r) -> r
    snat Z f = f SZ
    snat (S x) f = snat x (\x' -> f (SS x'))  </code>







[https://blog.jle.im/entry/introduction-to-singletons-2.html#the-existential-datatype](https://blog.jle.im/entry/introduction-to-singletons-2.html#the-existential-datatype)







Checkout the functions withSomeSing. These are the interfaces between the verified and unverified parts of the code.







One tempting conceptual way of dicussing this is that these domains make up different categories, and that various mappings are Functors?













The ConstraintKinds extension built a bridge between types and typeclasses.







The constraints library in my mind has some reminsecent flavor of singletons due to the use of the nearly trivial GADT Dict, but I don't think the two are all that similar  














The constraints library can reflect typeclasses into values.













Typeable reflects types into values I think.







Ghosts of departed proofs has a way of giving type names to values. This is very much at the discretion of a library/theory author.  








I actually don't know of ways to reflect into and out of rewrite rules



