

Other ideas:
A maze game. Pixel positions that are kinematic nbot using physics engines
A random 1d walk with a wall. Prove that can't teleport inside or between the rooms.



(bounce demo here.)

I think programs that use numbers are among the most interesting. Ray tracers, physics engines, differential equation solvers, curve fitters, optimizers, differentiators, geometry processing, CAD, generative art, molecular simulations, multiphysics solvers, matrix solvers,, etc.

Most of the material you find on Coq out there focuses on heavily symbolic topics like programming language theory and logic. 

What I mean by numbers is an interesting question. What is a number when you need to put it in a computer? The things that go into computers are not platonic numbers and they always have to choose a representation that is arbitrary and/or undesirable in some sense. Here are some examples.
- Machine Integers. ex: 64 bits two complements with overflow
- Machine Floating point numbers. Finite precision with rounding and some weird edge cases.
- BigInts. In principle infinitely sized integers with no overflow.
- Peano Numbers `data Peano = Zero | Succ Peano`
- MultiPrecision floating point - in principle you can get as much precision as you ask for
- Rationals. Pairs of some kind of integer data type for numerator and denominator
- Intervals - Kind of a number, kind of not. Kind of an approximate set of numbers. Stores two overapproximate endpoints of a range of numbers using one of the other representations.
- Algebraic numbers - stores a polynomial and interval which describes a root.

I have chosen a baby problem just to play around a bit.

It may be cheating a bit, but the only part I'm going to do in coq is the state update code. This may be a little disappointing but unsurprising, since the state update code can be easily seen to have a mathematical and well specified flavor to it. Gotta pick your battles.

First we consider what is the state? The state is the current position of the dvd logo corner and it's current velocity.
By using integer values for the state we will make our lives easier when it comes for coq time. This is not a fundamental limitation and perhaps a good subject for a future post.

We can store this in a javascript object like so.

## Naive Javascript Version

I intentionally tried to write this quickly while not thinking too hard. In the end of the day I'm not super sure that I have it bouncing exactly on the boundary, or that the dvd logo can't escape, but I'm pretty sure. The code is fairly simple after all

# Coq Version

## InBounds

forall init, InBounds init -> forall n, InBounds (repeat n step init)

## No Overflow

## The Master Theorem

Of course the most important theorem of a dvd bounce demo is that we want to guarantee that it will eventually exactly hit a corner regardless of the initial conditions.

forall init : state, exists n : nat, InCorner (repeat n step init).

## What's the point?

Well, there is no point. I have no burning need for a DVD bounce demo. This whole exercise is pissing in the wind.

More generally though, the point was that this is a stepping stone to using similar techniques on a problem i do care about for some reason. It would be nice if physics engines were verified robust such that two objects can never end up inside each other for example, or that certain kinds of overflow never occur.

I note that actually since I have chosen a finite state space, more so a fairly small finite state space, this problem can be verified by brute force checking. This may be more desirable. Brute force is so simple, and requires very little sophistication on the part of the user, that it is a very useful technique to consider. Brute force checkers can be written in any language, rather than relying on the symbolic capabilities of coq. The same can be said in ordinary programming. Sometimes using a table of precalculated results is better than actually implementing an algorithm for cosine on a microcontroller.
If we made out problem not so more complicated, brute force will become no longer a possibility.

### Compiling Coq to Javascript 

The chain I chose is extracting Coq to Ocaml and then compiling ocaml to javascript via the js_of_ocaml compiler. <https://ocsigen.org/js_of_ocaml/latest/manual/overview>

`dune` has some facilities for combined ocaml/coq projects and built in support for js_of_ocaml. <https://dune.readthedocs.io/en/stable/dune-files.html#coq-theory> <https://dune.readthedocs.io/en/stable/jsoo.html>




### Bits and Bobbles

What if I had chosen to use floats, as one might naively do, or as is more natural in a full fledged physics engine. Or even rationals? How do you deal with approximation systematically? A big question.

Using Javascript BigInt

A fairly small chunk of the program ultimately came from coq. There is a great deal written in javascript. The actual drawing code, the entire javascript runtime. What 

https://compcert.org/doc/html/compcert.lib.Integers.html

Math comp integers?

Coq club friday may 2021
 "
My reference setup when working with this kind of structures is to use
the `subType` pattern provided by the mathematical components library,
which is indeed applicable to any type of the shape:

{ x : T | P x } where P : T -> T -> bool [so irrelevance holds for free]

This provides reasonable support for both going to the base type, as
well as inferring the invariant for common operations [see for example
math-comp's tuple implementation]

For modular arithmetic, at least in the reasoning part, I find it easier
to work with the representation for ints used in math-comp again, which
re-defines the operations to be modular, then you can handle them using
the regular machinery for algebra. "

### Full Javascript Code
