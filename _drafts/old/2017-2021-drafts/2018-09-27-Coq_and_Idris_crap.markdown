---
author: philzook58
comments: true
date: 2018-09-27 22:02:43+00:00
layout: post
link: https://www.philipzucker.com/?p=1258
published: false
slug: Coq and Idris crap
title: Coq and Idris crap
wordpress_id: 1258
---

Other universes:

Russell O'Connor coq real numbers

https://arxiv.org/abs/0805.2438

ROSCoq

www.cs.cornell.edu/~aa755/ROSCoq/Confidential.pdf

type classes for real computation

https://arxiv.org/pdf/1106.3448

Math Components

https://math-comp.github.io/mcb/



http://corn.cs.ru.nl//pub.html

The coq standard library. Shoudl peek through

https://coq.inria.fr/library/



hs-2-coq

https://github.com/antalsz/hs-to-coq

coq analysis

https://github.com/math-comp/analysis

opam coq list

https://github.com/coq/opam-coq-archive/tree/master/released/packages

verdi

coq- intervals for interval arithmetic

http://coq-interval.gforge.inria.fr/

also flocq for floating point and coqulicot for real analysis

https://www.lri.fr/~melquion/





Coq hasekll correspondence



Inductive ~ data definition



Fixpoint ~ Recursive defintion

Definition ~ definition

match ~ case

tactics - build expressions with holes. When you're writing complicated functions, sometimes you can follow your nose. We I need to return a function, so let's put a lambda binder. Ok. how do the lego pieces come toegether.

induct case matches and then allows a recursive call. There is a hole for every case. The default case may be somewhat equivalent to semicolon chaining.

intros starts a lambda term and puts a hole in the body.

simpl does not have an obvious correspondence. Maybe like :kind! that requires you to actually ask for type families to fully evaluate?

reflexivity fills the hole with a Refl I think.

rewrite uses equalities. I don't know that Haskell gives you direct control of how it uses equality facts (a ~ b). It might not matter. Maybe. I think rewrite might be

case (usefulequality : z = q) of

| Refl => _the_rest_of_the_proof?

assert makes some kind of let expression.



The new? docs are really useful

[https://coq.inria.fr/refman/index.html](https://coq.inria.fr/refman/index.html)

exact and refine tactics let you prove stuff with direct functional programs. That's interesting.

Ltac is some kind of backtracking search language with pattern matching. Pattern matching on the needed type? Sounds like typeclass programming.

class Tactic goal newgoal | goalstack ctx -> newgoalstack

context is HList

class Intro ctx (a->b) (sym :: ctx) b where

intros :: sym -> a -> State ctx b. -- or (State ctx (a->b))?

intros @"a" .

do

intros @"a"

class Case ctx a

proof = runState



maybe combine or replace State with some kind of backtracking/nondeterministic monad.

I don't really need typeclasses for this stuff. Yet.



Agda





Cubical Type theory



https://www.youtube.com/watch?v=W5-ulP_JzNc






