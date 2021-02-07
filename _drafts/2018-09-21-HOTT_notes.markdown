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

Higher inductive types are where it is actually at I guess.

https://www.youtube.com/watch?v=A6hXn6QCu0k emily reihl - inifnity categroeis for undergrads, but really it's about homotopy type thoery

11/2020 
https://github.com/HoTT-Intro/Agda
I screwed up my emacs agda by having a rotten tuareg in it. I think
https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

https://pure.itu.dk/portal/files/84649948/icfp19main_p164_p.pdf - ICFP cubical agda, a depdently typed programming language with higher inductive types. Interestingly, from Mertberg's demo, I feel like the emphasis was not on cubical itself. More interested in standard HoTT they just want it to be better


HoTT - quotients supposedly? Fractions? Integers vs naturals. I guess that's the zeroth.
Or maybe True / False modulo True = False?
Anders Morberg - cubical agda  https://vimeo.com/459020971

data _===_ {A : Set} (x : A) : A -> Set where
  refl : x == x

funExt

replcace inductive === with paths

{-# OPTIONS -- cubical #-}
open import Cubival.Foundations.Prelude
                        Equiv
                         Isomorphism
                         Univalence
                         Cubical.Data.Int
                         Cubical.Data.prod

-- I , npoitns i0, i1
apply0 : (A; Type ) -> (p : I -> A) -> A
apply0 A p = p i0

refl' : {A : Type} (x : A) -> x \== x -- PathP (\ _ -> A) x x
refl' x = \i -> x

-- x \== x  h means PathP (\ _ -> A) x y
-- path over path. depednent paths

cong' : {A B : Type} (f : A -> B) {x y : A} -> x == y -> f x == f y
cong' f p = \ i -> f ( p i )

funext'  : {A B : Type} (f g : A -> B) {x y : A} -> ( p: x : A ->  f x == g y ) -> f == g
funext p i = \x -> p x i

transport' : {A B : Type} -> A == B -> A -> B
trasnport' p x = transp (\i -> p i) i0 x

-- another primitive called hcomp

ua' :  {A B : Type} -> A ~ B -> A == B
ua' e = ua e

isToEquiv' : {A B :type} -> Iso A B -> A ~ B
isToEquiv' e =  isoToEquiv e

isoToPath : Iso A B -> A == B
isoToPath e = ua (isoToEquiv e) 

data Bool : Type where
   false : Bool
   true : Bool

not : Bool -> Bool
not false = true
not true = false

notPath : Bool === Bool
notPath = isoToPath' (iso  not not rem rem)
  where 
  rem : (x : Bool) -> not (not x) == x
  rem false = refl
  rem true = refl 

transport notPath true -- false

sucPath : Int === Int
sucPath = (isoToPath' (iso sucInt predInt sucPred redSuc)

transport ( sucPath . sucPath) (pos 4) 

-- multisets

data FMSet (A : Type) : Type where
   [] : FMSet A
   _::_ : A -> FMSet A -> FMSet A
   comm : ( x y : A) (xs : FMSet A) -> 
         x :: y :: xs == y :: x :: xs
    trunc : isSet (FMSet A) -- UIP

_++_ : {A : Type} -> FMSet A -> FMSet A -> FMSet A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)
(comm x y xs i) ++ ys = comm x y (xs ++ ys) i

-- can prove all kinds of things : xs ++ [] == xs ...

Cubical.HITs.FiniteMultiSet

unitr-++ : {A : Type} (xs : FMSet) -> xs ++ [] == xs
unitr++ [] = refl
unitr++ (x :: xs) =    

SIP structure idenity principle
Cubical.Algerba.Monoid.Base -- reflection

queues, matrices. Huh. representiation independence transportiung proofs.



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

