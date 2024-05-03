---
author: philzook58
comments: true
date: 2017-09-10 17:54:46+00:00
layout: post
link: https://www.philipzucker.com/?p=874
published: false
slug: Type Theory
title: Type Theory
wordpress_id: 874
---

What is type theory?

I'm not sure. I went down a long road with it, then left to classical logic land, and now I shall return.



 	
  1. Types like int and string somehow guarantee in a C program that you never use something as if it were an int even though it is a string. There is an implicit _proof _of this fact in the type checker. How does it know that the huge number of possible incomparable type errors didn't occur? It's kind of remarkable. It could tell you how it knows if you look at the internals of the type checker. When you declare a variable as a type, you are making an axiomatic statement that it is indeed that type.

 	
  2. In mathy set land, type theory can be thought of as kind of a strictified version of set theory. The number 4 is an element of the natural numbers. But it is also an element of the set {4}. Elements seem to have some kind of identity external to just being a part of the set they're in. In type theory, that isn't the case. The set to which it is an element of is a vital part of what the thing is. It does feel like the 4 in {4} is somehow the same 4 in the naturals, but let's play the game. A theory of this equality perhaps can be developed down the line on top of the structure that says the set is an important aspect of the element. Why is this important? Formalizing things in this way helps avoid paradoxes. You can't have sets that are in themselves. (See Russell's Paradox).

 	
  3.   Logic land. 12 : int, "hello":string,  and 4:Nats. Sort of the colon is like the "element of" operator. But also you can look at something like proof:Proposition. This is a curious way of looking at logic. Logic is not really such a god given system in the sense that there appears to be one agreed on. Logic becomes kind of a formal game. You have a couple of ways of rewriting expressions.

 	
  4. Category theory land.




Some simple observations about set theory can be

B <= (A u B) n (B u C)

Relations. In first order logic Relations are binary predicates. In set theory, relations are. Relations are interesting. They don't have the one way-ness to them functions do. They have a sense of searching. Multiparameter Typeclasses form relations. The type checker does not like ambiguous situations. Relations are ambiguous. Multiparameter typeclasses are programmed somewhat like prolog.

Forward reasoning and backward reasoning are connected to introduction and elimination rules. There is a sense of conservation, that things are pushed around but never lost. The Haskell Book of Logic has the best explanation of this I've seen, in very clear english (not even haskell actually).

Given:

To Be Proved:

The Given are the things in Gamma. The surrounding programming context. Axiomatic primal functions and values.

For implications, the way you prove is is to suppose the thing holds. This allows you to put it in your gamma, in your naming context. In a programming context, this means, "suppose you've truly given me an Int. Then this is how i will give you the thing you desire"







names have power. The ability of 4 to have a name or a set to have a name is what leads to paradoxes. Names allow the logic to reach around non-locally. It allows the thing to exist in a manner separate to what it is. Category theory and point free style has no names. The thing is what it does.

The operations of logic:



Type checking is just seeing if you used the rules in valid ways. That is quite easy. Program running is using an implication to derive the

The programs of logic:

Unification: Finds a way of consistently instantiating variables

Pattern Matching.



Conversion between a statement and it's proof is hard.

The program is another way of writing the Gentzen Sequent Calculus. The proof tree is the same as the syntax tree.



Propositional Calculus - similar to simply typed lambda calculus

First Order Logic - similar to parametric typed lambda calculus



One of the best books on classical logic is actually Norvig and Russell's AI book.



Dependent Types - The lambda calculus is a theory of substitution. In some sense, this is what a function is. You have some expression that specifies how to take an arbitrary element x to some y. Then you actually substitute in the value 3 let's say. Now some confusion comes from \x->x*x. Subsitution makes this 3*3. But that isn't really 9 is it? Well, that's because you've got this crazy not-very-mathematical numeral system tagged on. So you need to add all kinds of axioms that deal with 3 and 4 and what have you.

It helps perhaps to not visualize sets as some bag of objects, but consider the whole endeavor of sets to be some strange word game. Every function is some wordy spec on how to convert elements of a into elements in b. I think this is restrictive. Some functions require tough searching to compute them. We're talking very trivial functions. Try to think about discrete sets. You can specify the entire thing using cases. Then maybe we could move on to the naturals. I have no idea how to move on to the reals, but computers only have doubles anyhow, and any actually finitely computing function just returns rationals or algebraic representations of reals, which are more or less built by taking the symbol pi to be some kind of axiom you're allowed to start with and then having some finite expression tree structure or something.

What is the difference between terms and types? What is the difference between elements and Sets? A set can be an element in a set of sets.  So it depends on context. It is acceptable to pull terms up into types, but not acceptable to pull types down into terms (lambda cube paper does not agree. says \x:A->x is pulling type into term)? Why and what does this really mean? There is a partial ordering of termier and typier. 3 is termier than {3,4} and also termier than {{3,4}}. 3 and 4 are equally termy. There may be things that are totally incomparable in this way.

What is the difference between functions and constructors? Constructors are of the type *->* ? It sure seems like Left for example, has the type o a function from a -> Either a b, but it was clearly defined differently from other functions.



What is the difference between a lambda and a pi? Lambda occurs on the left hand side of the typing colon, pi is on the right side.

In the set theory interpretation, A->B is the set of functions from A to B

A category has types and arrows. Functors are like . A category with only identity morphisms may be the closest to a pure set. Then the functors between them are functions.

Alternatively the base case can be thinking of categories are a collection of sets and the morphsims as functions between sets.



Theorems about theorems. https://en.wikipedia.org/wiki/Principle_of_explosion.



In the sense that an element has no identity beyond the set it belongs to, the union and complement

Cartesian Product is the pair type.

Disjoint/Tagged Union is the sum/Either type.

Pullbacks and Pushouts are unions and interesections? Is that right?


