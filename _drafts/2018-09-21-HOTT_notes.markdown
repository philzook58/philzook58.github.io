---
author: philzook58
comments: true
date: 2018-09-21 18:49:59+00:00
layout: post
link: https://www.philipzucker.com/?p=1302
published: false
slug: HOTT notes
title: HOTT notes
wordpress_id: 1302
---
11/2020 
HoTT - quotients supposedly? Fractions? Integers vs naturals. I guess that's the zeroth.
Or maybe True / False modulo True = False?
Anders Morberg - cubical agda  https://vimeo.com/459020971
https://arxiv.org/abs/1701.04391 - de moura selsam. good explanation of equality type
John Major equality - conor mcbride
Doing raw recursor proofs. Can I do it? I feel like it's kind of straightforward.
Begin able to write out exactly where I want the equality applied via a lambda. 
Could Axiomatize equality rather than use Inductive definition.
The pattern match of a HIT must desguar into recursors?


Types are spaces.
values are points
dependent types are fibrations
identity types are paths


Other weirdness:
Observational type theory

Describing a concrete simplex as a gadt.
How do you make a correct by construction data structure of a path?
A list of vertices. Fine. But is there a path between each of them?
Ok, list of edges. Do those edges meet?





9/2018

univalence let's you turn isomorphisms into equality and get isomorphisms out of equalities.

HIT - Higher inductive types. Instead of always needing the data constructor to end with the type itself A , now it can end with =_A also. You can do this using

recursors. Patrern matching is cool,. but it can be desgared into something else. A function that takes a continuation for each case of the type.

focus on inclusion and projection maps of the basic simplex

Cubical Sets.

of of the basic interval.

Simpilical Sets.

By using the basic simplex with its inclusion maps as sort of a index into your complex, you can grab all n-simplices at once. This is a Functor relation.

$latex

Great intro

https://arxiv.org/pdf/0809.4221

You can use a postulate methodology where you slam out all the pieces of your type as axioms

Dan Licata explaining how to use hiding to implement HIT. You export an interface. This let's you postulate less

https://homotopytypetheory.org/2011/04/23/running-circles-around-in-your-proof-assistant/

Homotopy group of circle is Z

https://homotopytypetheory.org/2012/06/07/a-simpler-proof-that-%CF%80%E2%82%81s%C2%B9-is-z/

https://www.cs.cmu.edu/~drl/pubs/ls13pi1s1/ls13pi1s1.pdf

You always need streicher K and rewriting turned on. What do these do?

https://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/

https://stackoverflow.com/questions/39239363/what-is-axiom-k/39256457

Axiom K is Uniqeness of Identity Proofs. Default pattern matching allows this. Modified pattern matching doesn't. The recursor form doesn't seem to have this problem

    
    uip : {A : Set} -> {a : A} -> (p q : a ≡ a) -> p ≡ q
    uip refl refl = refl

https://github.com/HoTT/HoTT-Agda

Kind of hard to navigate. Like the std-lib but harder.

Useful start in core. Check out univalence, check out the types folder. Look at the normal types like Bool, Nat, List. Now check out Circle, Torus,

Interesting lectures using cubicaltt

https://github.com/mortberg/cubicaltt/tree/master/lectures

