---
layout: post
title:  "Mathematical Logic Part 1"
date:   2017-07-10 16:16:01 -0600
categories: jekyll update
---


Let me describe my journey.
In high school, I got this book "Bebop to the Boolean Boogie", which I loved. It explainbed the basics 
I got an engineering physics degree and took some digital logic courses.
So to me, logic was basically And, Or, Xor. Really what could be said that is that interesting about those? It's pretty cool that you can eventually build higher level styructures out of them like adders and multiplexers, but there isn't much to say about the gates.
I came across Haskell at a meetup maybe 3 years ago. Someone was mentioning that they were trying to learn it. I gave LYAHG a couple tries before I basically got through it with many months in between attempts. It was not high on my list.
But at a certain point I thought it was pretty cool and I liked the kind of clever and clean feeling typed functional programming had.
Then I think I saw a Strangeloop video by Philip Wadler on the Curry Howard Correspondence.
And I read the denotational Semantics section of the Haskell Wiki.
And eventually I even tried my hand at Coq and Agda and Idris, although I'm still at the struggling level with all of them still, similar to the place I was at with haskell in the beginning, where I give it another shot every 6 months maybe.
So  was first introduced to logic really

And now I've been seeing a bit of Prolog and learning about SAT solvers and SMT. All these things are connected and very interesting.

So the most basic question you might ask is what does a boolean expression evaluate to?
This is very simple to do by hand.
Posing the question concretely on a computer requires you to think about the data structure you would like to use to phrase the problem. My first inclination is to use a Expression tree and build an evaluator.

You could do the  same thing for a simple calculator with plus and times.

It even feels rather similar, since in a sense time is very much like And and plus is like Or.





Substitution


CNF

Model Checking

Proofs

Resolution

SAT

Why do you want SAT? It's an interesting search problem. Many tough search problems can be reduced to SAT
SAT tricks

Data Structures - BDDs



Unification









How can you reason about infinite things?

The axiom of induction



\forall