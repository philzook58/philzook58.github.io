---
author: philzook58
comments: true
date: 2016-10-09 20:13:59+00:00
layout: post
link: https://www.philipzucker.com/?p=524
published: false
slug: Fix and Types. F-algebras?
title: Fix and Types. F-algebras?
wordpress_id: 524
---

So I'm in the process of having some revelations about a very cryptic sounding and seeming subject: fixpoints and F-Algebras.

There is a function fix

    
    fix :: (a -> a) -> a
    fix f = let x = f x in x


[https://en.wikibooks.org/wiki/Haskell/Fix_and_recursion](https://en.wikibooks.org/wiki/Haskell/Fix_and_recursion)

Now this fix is described as being used to recursify functions. This is an interpretation that the type a above matches a function type. Then the input f is a function from functions to functions (b -> c) -> (b -> c) i.e. we've replaced a = (b->c). Using fix on this returns another function. In this way for example we can define a factorial function from the higher order function that takes any function  f' and returns n * f' (n-1) if n > 0 and 1 if n = 0. It's a screwy way to make a factorial.

That's pretty complicated. But just looking at fix in terms of a, then it is simpler but unbelievable. fix somehow takes a function where the range is the same as the domain and mangles it somehow into a value in the domain. That is the thing to keep in mind. That is the more fundamental idea rather than recursifying functions.

Its like I gave you f(x) = x^2 -7 a function from numbers to number and told you to return me a number. What number? 47? 184? These would just be constants, I'd sort of be throwing away f. That doesn't seem useful.

Well.... The fixed point of the function is a somewhat natural suggestion. Solving f(x)=x does give a number. One method to generate successive approximations is to just iterate the function on itself. In some cases, this will decrease your distance to the fixed point. In general that is hard to do though. How could one algorithmically exactly solve that?

fix doesn't quite do the same thing as that example suggests. Its similar enough to be confusing.

fix finds the least fixpoint in the domain theory sense. The problem is that functions in computers are not like x^2-7. Sometimes they don't terminate. So a function's return value might just be to hang. There is a sense in which this value of hanging (called bottom) is less than the number 3. And in a lazily evaluated language there is a hierarchy ordering possible hanging conditions. If the program were to investigate some value, it would hang, but lazy evaluation doesn't always investigate every value.

[https://en.wikibooks.org/wiki/Haskell/Denotational_semantics](https://en.wikibooks.org/wiki/Haskell/Denotational_semantics)

The trouble with being handed a fully functioning Haskell is that you cannot appreciate something like this. I can already define recursive functions. Easily. It seems idiotic to go through this confusing intermediary.

If one were to be building a language from scratch, you have to give the language fundamental powers. Primitive operations that can be combined (this combination is also a fundamental power) to create complicated ones. These powers don't necessarily have to be orthogonal. From a reality of computing perspective, it makes sense to make your fundamental powers things hardcoded into the common architecture of cpus. 32, 64 bit integer ops, floats, bit operations, maybe memory shuffling.

From the 1000foot view it makes sense to define your starting point in terms of things that are mathematically elegant, a small tight orthogonal set of axiomatic powers that draw inspiration from some big incomprehensible math book. Then the responsibility of mapping this small set into hardware can be done fairly dumbly if you don't care about performance, or someone can spend a great deal of time ( SPJ?) making the mapping really nice.

Haskell has polymorphic types. They support defining types with type variables and self referential definitions. This is pretty crazy, and useful.But complicated. It feels like you have lambda abstraction aka function definition sort of at the type level, which is cool.

What's the minimum viable thing that feels like type variables?

Reading Harper's Practical Foundations for Programming languages, I get the feeling that surprisingly the simplest possible thing is to bake Functor definition and Map as fundamental powers in your language. Functor is sort of a 1 type variable type. map is the dynamical evaluation power that your need to use functors in any interesting way.

Given that, another interesting power you can give is Fix aka Mu. This let's you convert a Functor type (Type -> Type) into just a type (Type)

In other words Fix is (Type->Type) -> Type or  Functor -> Type.

Now to use the Fix type in an interesting way, we need to introduce more powers like we did with map. Harper calls them fold and rec.




