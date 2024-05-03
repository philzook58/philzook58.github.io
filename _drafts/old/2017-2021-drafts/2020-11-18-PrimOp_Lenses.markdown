---
author: philzook58
comments: true
date: 2020-11-18 15:13:05+00:00
layout: post
link: https://www.philipzucker.com/?p=3011
published: false
slug: PrimOp Lenses
title: PrimOp Lenses
wordpress_id: 3011
---




The lens is a function of the type `s -> (a, b -> t)`. This type can be used as a functional bundling of getter and setter functions. It is interesting that one can define a notion of composition for this type.







Divorced from this notion of getters and setters, this type can be seen as prescribing a certain kind of control flow, one in which there is a single pass forward and then a single pass backwards. 







An example of a lens type that is not getters and setters is one implementing reverse mode automatic differentiation aka Backpropagation. This is a highly studied and implemented algorithm. 







In this light, the type is a relative of those you might find in a coroutine library `data CoRoutine = AwaitForward s -> Coroutine | YieldForward a CoRoutine | AwaitBackward b -> Coroutine | YieldBackward t Coroutine | Done`. The lens is a subset of the behavior available in this type, specifically corutines of the form `AwaitForward (\s -> YieldForward (f s) (AwaitBackward (\b -> YieldBackward g s b Done )`







Coroutines are so named because they are a haskell representation of an older imperative concept. Back in the days of yore, programmer's were more in touch with the unstructured possibilities of assembly. A coroutine is an interruptible subroutine. Whereas a subroutine is called and returned from,. coroutines live on more equal footing, calling each other back and forth.







When you say funky control flow, the functional programmer's response is "continuations".`(s, t -> r) -> (a, b -> r)   `is a continuation passing style implementation of a lens. Danvy there and back again. The implementation of continuations is interesting. In all programming languages, certain structures are made implicit. Even in assembly, to some degree the progress of the program counter is implicit. In C, the maniuplation and recording of the call stack is implicit. Sometimes i notice that depth fiurst search is more elegant to implement than breadth first, and this is because one can use the stack facilities already present. Alexis king primop CPS talk. This trick is sometimes called the Yoneda embedding. It is a manifestation of the yoneda embedding in Haskell. Bartosz Yoneda embedding (a -> s) -> (b -> s).







The stack has to store return addresses and the context from which a function was called. With a slight persepctive adjustment, it is another argument to any function. Forth also makes this persepctive more prominent. But so does CPS.







(s -> (e ,a )   , (e,b) -> t   is a closure converted formulation of a Lens. It can also be interpreted as explicitly demonstrating that getters and setter are breaking apart and building up a product type. The magic of the lens is that (b -> t) gets to tuck away some remembered information about s by closing over whatever it needs. Non garbage collected lagnauges like C++ and Rust with lambdas make this closure process much more explicit. 







Objects are codata. Codata can match on contexts rather than on data. Objects can be modeled as existential types. The only thing you can do with an object is send it a message. Closure objects are objects that accept the message that they are to be applied to arguments. 







Van Laarhoven lens `Functor f => ( a -> f b ) -> (s -> f t)`. How to interpret `f` in terms of implementation? A higher kinded type `f :: Type -> Type` is often thought of as a "container" or as an "effect". Leibnitz equality. This is also described as a "CPS" lens.







[https://kseo.github.io/posts/2016-12-10-encodings-of-lense.html](https://kseo.github.io/posts/2016-12-10-encodings-of-lense.html)







  * Source to Source
  * Computation Graphs
  * Wengert Tapes






The Wengert tape is a kind of shadow stack.







Wengert tape can be thought of a language to be interpreted or bytecode.













Profunctor Lens. Optics are perspective in which the lens is not the primary thing of interest, but instead it's generalizations.







Dialectica nad Lens. Jules hedges blog post. Piedrot's thesis and talks. there is something tantalizing here



