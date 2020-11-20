---
author: philzook58
comments: true
date: 2019-12-29 04:33:06+00:00
layout: post
link: https://www.philipzucker.com/more-stupid-z3py-tricks-simple-proofs/
slug: more-stupid-z3py-tricks-simple-proofs
title: 'More Stupid Z3Py Tricks: Simple Proofs'
wordpress_id: 2600
categories:
- Formal Methods
tags:
- z3
---




Z3 can be used for proofs. The input language isn't anywhere near as powerful as interactive theorem provers like Coq, Isabelle, or Agda, but you can ask Z3 to prove pretty interesting things. Although the theorems that follow aren't hard in interactive theorem provers, they would take beyond complete novice level skills to state or prove.







I like to think of the z3 proving process as "failing to find a counterexample". Z3py has supplies a function `prove` which is implemented like this.





[gist https://gist.github.com/philzook58/40634d9be7a52e760476d041c9299c4e#file-prove-py]





Basically, it negates the thing you want to prove. It then tries to find a way to instantiate the variables in the expression to make the statement false. If it comes back unsat, then there is no variable assignment that does it. Another way to think about this is rewriting the $latex \forall y. p(y) $ as $latex \neg \exists y \neg p (y)$.  The first $latex \neg$ lives at sort of a meta level, where we consider unsat as a success, but the inner $latex \neg$ is the one appearing in `s.add(Not(claim))`.







We can prove some simple facts. This is still quite cool, let's not get too jaded. Manually proving these things in Coq does suck (although is easy if you use the ring, psatz, and lra tactics [https://coq.inria.fr/refman/addendum/micromega.html](https://coq.inria.fr/refman/addendum/micromega.html), which you DEFINITELY should. It is a great irony of learning coq that you cut your teeth on theorems that you shouldn't do by hand).





[gist https://gist.github.com/philzook58/40634d9be7a52e760476d041c9299c4e#file-simple-py]





Ok, here's our first sort of interesting example. Some properties of even and odd numbers. Even and Odd are natural predicates. What are possible choices to represent predictaes in z3?  
We can either choose python functions `IntSort -> BoolSort()` as predicates or we can make internal z3 functions `Function(IntSort(), BoolSort())`





[gist https://gist.github.com/philzook58/40634d9be7a52e760476d041c9299c4e#file-even-py]





All well and good, but try to prove facts about the multiplicative properties of even and odd. Doesn't go through. :(







Here's a simple inductive proof. Z3 can do induction, but you sort of have to do it manually, or with a combinator. Given a predicate f, inductionNat returns





[gist https://gist.github.com/philzook58/40634d9be7a52e760476d041c9299c4e#file-induction-py]





Here's another cute and stupid trick. Z3 doesn't have a built in sine or cosine. Perhaps you would want to look into [dreal](http://dreal.github.io/) if you think you might be heavily looking into such things. However, sine and cosine are actually defined implicitly via a couple of their formula. So we can instantiate   
A slightly counterintuitive thing is that we can't use this to directly compute sine and cosine values. That would require returning a model, which would include a model of sine and cosine, which z3 cannot express.  
However, we can try to assert false facts about sine and cosine and z3 can prove they are in fact unsatisfiable. In this way we can narrow down values by bisection guessing. This is very silly.





[gist https://gist.github.com/philzook58/40634d9be7a52e760476d041c9299c4e#file-trig-py]





A trick that I like to use sometimes is embedding objects in numpy arrays. Numpy slicing is the best thing since sliced bread. A lot, but not all, of numpy operations come for free, like matrix multiply, dot, sum, indexing, slicing, reshaping. Only some are implemented in terms of overloadable operations. here we can prove the Cauchy Schwartz inequality for a particular vector and some axioms of vector spaces.





[gist https://gist.github.com/philzook58/40634d9be7a52e760476d041c9299c4e#file-np-py]





Defining and proving simple properties of Min and Max functions





[gist https://gist.github.com/philzook58/40634d9be7a52e760476d041c9299c4e#file-minmax-py]





Proving the[ Babylonian method](https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Babylonian_method) for calculating square roots is getting close to the right answer. I like the to think of the Babylonian method very roughly this way: If your current guess is low for the square root x/guess is high. If your guess is high, x/guess is low. So if you take the average of the two, it seems plausible you're closer to the real answer. We can also see that if you are precisely at the square root, (x/res + x)/2 stays the same. Part of the the trick here is that z3 can understand square roots directly as a specification. Also note because of python overloading, `babylonian` with work on regular numbers and symbolic z3 numbers. We can also prove that babylon_iter is a contractive, which is interesting in it's own right.





[gist https://gist.github.com/philzook58/40634d9be7a52e760476d041c9299c4e#file-bab-py]





A funny thing we can do is define [interval arithmetic ](https://en.wikipedia.org/wiki/Interval_arithmetic)using z3 variables. Interval arithmetic is very cool. Checkout [Moore's book](http://www-sbras.nsc.ru/interval/Library/InteBooks/IntroIntervAn.pdf), it's good. This might be a nice way of proving facts related to real analysis. Not sure.  
This is funny because z3 internally uses interval arithmetic. So what we're doing is either very idiotically circular  or pleasantly self-similar.  
We could use a similar arrangement to get complex numbers, which z3 does not natively support





[gist https://gist.github.com/philzook58/40634d9be7a52e760476d041c9299c4e#file-interval-py]

