---
author: philzook58
comments: true
date: 2020-01-25 19:27:13+00:00
layout: post
link: https://www.philipzucker.com/a-sketch-of-categorical-relation-algebra-combinators-in-z3py/
slug: a-sketch-of-categorical-relation-algebra-combinators-in-z3py
title: A Sketch of Categorical Relation Algebra Combinators in Z3Py
wordpress_id: 2627
categories:
- Formal Methods
tags:
- categorytheory
- python
- z3
---




I've discussed relation algebra [before](http://www.philipzucker.com/a-short-skinny-on-relations-towards-the-algebra-of-programming/). Relations are sets of tuples. There, I implemented the relations naively using lists for sets. This is very simple, and very clean especially with list comprehension syntax.  It is however horrifically inefficient, and we could only deal with finitely enumerable domains. The easiest path to fixing these problems is to cash out to an external solver, in this case z3.







There are many beautifully implemented solvers out there and equally beautiful DSL/modeling languages. Examples in mind include sympy, cvxpy, and z3. These modeling languages require you to instantiate variable objects and build expressions out of them and then hand it off to the solver. This is a reasonable interface, but there are advantages to a more categorical/point-free style DSL. 







Point-free languages are ones that do not include binding forms that introduce bound/dummy variables. Examples of binding forms like this are $latex \lambda \sum \max \min \int \sup \lim \forall \exists$.  One problem lies in the fact that the names of bound variables don't matter, and that they end up accidentally smashing into each other.  You may have experienced this in physics or math class as the dummy indices or dummy variable problem causing you to screw up your calculation of some cross product identity or some complicated tensor sum. These are surprisingly subtle problems, very difficult to diagnose and get right. de Bruijn indices is a technique for giving the bound variables canonical names, but it sucks to implement in its own way. When you make a DSL point free, it is a joy to manipulate, optimize, and search. I think this may be the core of why category theory is good language for mathematics and programming.







Point-free style also tends to have significant economy of size, for better or worse. Sometimes it is better to have an expression very dense in information. This is important if you are about the algebraically manipulate an expression with paper and pencil. Every manipulation requires a great deal of mind numbing copying as you proceed line by line, so it can be excruciating if your notation has a lot of unnecessary bulk.







Relations are like functions. The two pieces of the tuple can be roughly thought of as the "input" and the "output". Relations are only loosely directional though. Part of the point of relations is that the converse (inverse) of a relation is easy to define.







When we are implement relations, we have a choice. Do we want the relation to produce its variables, accept its variable, or accept one and produce the other? There are advantages to each. When relations were [(a,b)], a -> b -> Bool, and a -> [b] converting between these forms was a rather painful enumeration process. The sting of converting between them is taken out by the fact that the conversion is no longer a very computationally expensive process, since we're working at the modeling layer. 







When you're converting a pointful DSL to pointfree DSL, you have to be careful where you instantiate fresh variables or else you'll end up with secret relations that you didn't intend. Every instantiation of `id` needs to be using fresh variables for example. You don't want the different `id` talking to each other.  Sometimes achieving this involves a little currying and/or thunking.







There is a pattern that I have notice when I'm using modeling languages. When you have a function or relation on variables, there are constraints produced that you have to keep a record of. The pythonic way is to have a Model or Solver object, and then have that objects mutate an internal record of the set of constraints. I don't particularly enjoy this style though. It feels like too much boiler plate. 







In Haskell, I would use something like a Writer monad to automatically record the constraints that are occurring. Monads are not really all that pleasant even in Haskell, and especially a no go in python without "do" syntax.







However, because we are going point free it is no extra cost at all to include this pipework along for the ride in the composition operation.







Here are implementations of the identity and composition for three different styles. Style 1 is fully receptive, style 2 is mixed (function feeling) and style 3 is fully productive of variables.







Fair warning, I'm being sketchy here. I haven't really tried this stuff out.





[gist https://gist.github.com/philzook58/328a29e64cf740c62cbe2138913b59a2#file-idcomp-py]





z3 is a simply typed language. You can get away with some polymorphism at the python level (for example the == dispatches correctly accord to the object) but sometimes you need to manually specify the sort of the variables. Given these types, the different styles are interconvertible





[gist https://gist.github.com/philzook58/328a29e64cf740c62cbe2138913b59a2#file-convert-py]





We can create the general cadre of relation algebra operators. Here is a somewhat incomplete list





[gist  https://gist.github.com/philzook58/328a29e64cf740c62cbe2138913b59a2#file-combinators-py]





Questions about relation algebra expressions are often phrased in term of relational inclusion. You can construct a relation algebra expression, use the rsub in the appropriate way and ask z3's `prove` function if it is true.





[gist https://gist.github.com/philzook58/328a29e64cf740c62cbe2138913b59a2#file-properties-py]

















Z3 has solvers for







  * Combinatorial Relations
  * Linear Relations
  * Polyhedral Relations
  * Polynomial Relations
  * Interval Relations - A point I was confused on. I thought interval relations were not interesting. But I was interpetting the term incorrectly. I was thinking of relations on AxB that are constrained to take the form of a product of intervals. In this case, the choice of A has no effect on the possible B whatsoever, so it feels non relational. However, there is also I_A x I_B , relations over the intervals of A and B. This is much closer to what is actually being discussed in interval arithmetic.  






Applications we can use this for:







  * Graph Problems. The Edges can be thought of as a relation between vertices. Relation composition Using the `starn` operator is a way to ask for paths through the graph.
  * Linear Relations - To some degree this might supplant my efforts on linear relations. [http://www.philipzucker.com/linear-relation-algebra-of-circuits-with-hmatrix/](http://www.philipzucker.com/linear-relation-algebra-of-circuits-with-hmatrix/) Z3 is fully capable of understanding linear relations.
  * Safety and liveness of control systems. Again. a transition relation is natural here. It is conceivable that the state space can be heterogenous in time, which is the interesting power of the categorical style. I feel like traditional control systems usually maintain the same state space throughout.
  * Program verification
  * Games? Nash equilibria?






### Other Thoughts







  * Maybe we are just building a shitty version of alloy. [https://alloytools.org/](https://alloytools.org/)
  * What about uninterpeted relations? What about higher order relations? What about reflecting into a z3 ADT for a relational language. Then we could do relational program synthesis. This is one style, just hand everything off to smt. [https://github.com/nadia-polikarpova/cse291-program-synthesis/tree/master/lectures](https://github.com/nadia-polikarpova/cse291-program-synthesis/tree/master/lectures)
  * I should try to comply with python conventions, in particular numpy and pandas conventions. @ should be composition for example, since relation composition has a lot of flavor of matrix composition. I should overload a lot of operators, but then I'd need to wrap in a class :(
  * Z3 has special support for some relations. How does that play in?  [https://theory.stanford.edu/~nikolaj/programmingz3.html#sec-special-relations](https://theory.stanford.edu/~nikolaj/programmingz3.html#sec-special-relations) [https://z3prover.github.io/api/html/ml/Z3.Relation.html ](https://z3prover.github.io/api/html/ml/Z3.Relation.html)
  * As long as you only use composition, there is a chaining of existentials, which really isn't so bad.
  * What we've done here is basically analogous/identical to what John Wiegley did compiling to the category of z3. Slightly different in that he only allowed for existential composition rather than relational division. [http://newartisans.com/2017/04/haskell-and-z3/](http://newartisans.com/2017/04/haskell-and-z3/)
  * We can reduced the burden on z3 if we know the constructive proof objects that witness our various operations. Z3 is gonna do better if we can tell it exactly which y witness the composition of operators, or clues to which branch of an Or it should use.
  * It's a bummer, but when you use quantifiers, you don't see countermodels? Maybe there is some hook where you can, or in the dump of the proof object.
  * What about recursion schemes? The exact nature of z3 to handle unbounded problems is fuzzy to me. It does have the support to define recursive functions. Also explicit induction predicates can go through sometimes.  Maybe look at the Cata I made in fancy relaion algebra post
  * I think most proof assistants have implementations of relation algebra available. I find you can do a surprising amount in z3. 


