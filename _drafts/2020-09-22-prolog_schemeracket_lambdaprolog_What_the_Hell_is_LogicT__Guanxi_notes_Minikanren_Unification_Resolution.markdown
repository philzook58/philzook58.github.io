---
author: philzook58
comments: true
date: 2020-09-22 15:37:08+00:00
layout: post
link: https://www.philipzucker.com/?p=1865
published: false
slug: prolog, scheme,racket, lambdaprolog, What the Hell is LogicT / Guanxi notes
  Minikanren, Unification, Resolution
title: prolog, scheme,racket, lambdaprolog, What the Hell is LogicT / Guanxi notes
  Minikanren, Unification, Resolution
wordpress_id: 1865
---




Propagators.







Kmett. The Art of the Propagator https://dspace.mit.edu/bitstream/handle/1721.1/44215/MIT-CSAIL-TR-2009-002.pdf?sequence=1&isAllowed=y 







The gecode manual [https://www.gecode.org/doc-latest/MPG.pdf](https://www.gecode.org/doc-latest/MPG.pdf)

























Adding constraints or smt. I have a seperate store for them (in the state)? explicit probe annotations to check still satisfiable.







9/1/20







I was looking at prolog again. Jesus nothing changes.







What are the good programs. The art of prolog has an open access link







Difference lists are cool. They really are similar ot hughes lists. Or al ist that keeps a pointer to it's end







Using it for theorem proving is cool. Where are those examples? The lambda prolog book has some exmaples. There is a propsitional satisfiabilioty prover in art of prolog. Propositional solver in powr of prolog [https://www.metalevel.at/prolog/theoremproving](https://www.metalevel.at/prolog/theoremproving) [http://vidal-rosset.net/g4i_prover.html](http://vidal-rosset.net/g4i_prover.html)   http://jens-otten.de/tutorial_cade19/slides/prover_tutorial_CADE19_2.pdf







[http://tca.github.io/veneer/examples/editor.html](http://tca.github.io/veneer/examples/editor.html) minikanren examples. 







[http://io.livecode.ch/](http://io.livecode.ch/) more minikanren examples [https://www.youtube.com/watch?v=0FwIwewHC3o](https://www.youtube.com/watch?v=0FwIwewHC3o) implementing microkanren 








https://www.youtube.com/watch?v=0FwIwewHC3o








nomial logic programming [https://arxiv.org/pdf/cs/0609062.pdf](https://arxiv.org/pdf/cs/0609062.pdf) alphaprolog. Chris mentioned this nominal thing as nother way of dealing with binders







Datalog - souffle.  Reading gorup paper [https://arxiv.org/pdf/1207.5384.pdf](https://arxiv.org/pdf/1207.5384.pdf). Sttratification. relations indexed on program point/ abstract state of program point. Interval analysis encoded in binary to datalog?



















425/20 I was playing with prolog recently. Pretty cool 







What is the deal with scheme and racket? i just don't have the  revelation.







[http://home.pipeline.com/~hbaker1/CheneyMTA.html](http://home.pipeline.com/~hbaker1/CheneyMTA.html)







Lisp in easy pieces







[http://cs.brown.edu/~sk/Publications/Books/ProgLangs/2007-04-26/](http://cs.brown.edu/~sk/Publications/Books/ProgLangs/2007-04-26/)







[https://schemers.org/](https://schemers.org/)



















I was looking at disjoint set data structures again [https://en.wikipedia.org/wiki/Disjoint-set_data_structure#cite_note-Conchon2007-9](https://en.wikipedia.org/wiki/Disjoint-set_data_structure#cite_note-Conchon2007-9)







Kmett's latest propgator talk was mentioning using group actions somehow in unification? [https://www.youtube.com/watch?v=s2dknG7KryQ](https://www.youtube.com/watch?v=s2dknG7KryQ)







george wilson - https://www.youtube.com/watch?v=nY1BCv3xn24 intutition for propagators.







[http://hackage.haskell.org/package/discrimination-0.3](http://hackage.haskell.org/package/discrimination-0.3) What the hell is this? Fritz Henglein. 







[http://conway.rutgers.edu/~ccshan/wiki/blog/posts/WordNumbers1/](http://conway.rutgers.edu/~ccshan/wiki/blog/posts/WordNumbers1/)








https://www.reddit.com/r/haskell/comments/a9yze4/is_there_an_arraylike_data_structure_which_gives/


interesting comments  






[https://www.lri.fr/~filliatr/puf/](https://www.lri.fr/~filliatr/puf/) a coq formalization of a persistent union find data structure.  They use persistent arrays, which do some kind of rebalancing operation. 







Persistent data structures. Wassup with them?







## 2019







Combine LogicT with an OSQP monad for branch and bound







[http://overtond.blogspot.com/2008/07/pre.html](http://overtond.blogspot.com/2008/07/pre.html)







[https://github.com/dmoverton/finite-domain](https://github.com/dmoverton/finite-domain)







[https://blog.plover.com/prog/haskell/monad-search.html](https://blog.plover.com/prog/haskell/monad-search.html)







[https://www.schoolofhaskell.com/user/chowells79/even-more-money](https://www.schoolofhaskell.com/user/chowells79/even-more-money)







[https://blog.jle.im/entry/unique-sample-drawing-searches-with-list-and-statet](https://blog.jle.im/entry/unique-sample-drawing-searches-with-list-and-statet)







Select Monad







Branch and Bound













Ed kmett is up to funny business







[https://www.youtube.com/watch?v=ISNYPKiE0YU&t=916s](https://www.youtube.com/watch?v=ISNYPKiE0YU&t=916s)







Propagators







[https://www.sciencedirect.com/science/article/pii/S1571066105805444](https://www.sciencedirect.com/science/article/pii/S1571066105805444)







Typed logical variables in haskell by Claesson and Ljundogjgklds







[https://people.seas.harvard.edu/~pbuiras/publications/KeyMonadHaskell2016.pdf](https://people.seas.harvard.edu/~pbuiras/publications/KeyMonadHaskell2016.pdf)







Also by claesson, the key monad paper. 







[http://www.cse.chalmers.se/~koen/](http://www.cse.chalmers.se/~koen/)







Interesting guy. He is coqauthor with hughes on quickcheck.







Atze van der Ploeg is both Key monad paper and reflection without remorse. They have an FRP paper that sounds interesting







He metnioend a number of interesting things. He's doing very reference heavy code? Kanren. 







He mentoins intension vs extensional equality. Judgemental eqaulity is the one inside the type checker. Is it ~ ? And intwnsional equality is the one within the language itself, that is :~: . Extensional. nuPRL starts with an untyped lambda calculus and then you teahc the system typing derivations? What is nuPRL's deal







Union-find algortihm - as part of unification?







nerualkanren, synquid. Two program synthetsis projects. Synquid uses liquid typing







Oleg Shen paper using efficient charing for logic programming







[https://www-ps.informatik.uni-kiel.de/~sebf/data/pub/icfp09.pdf](https://www-ps.informatik.uni-kiel.de/~sebf/data/pub/icfp09.pdf)







[http://sebfisch.github.io/explicit-sharing/](http://sebfisch.github.io/explicit-sharing/)







Maybe sebastein fischer is the name I should assicuate more storngly?







[https://sebfisch.github.io/research/](https://sebfisch.github.io/research/)







The Curry language. Haskell + logic. Egison has weirdo patterns too. Multiple patterns can match? Non-linear pattern require. Realted to view patterns? view patterns are a weirod syntax. realted to guard patterns. DOn't need to introduce intermediate names







[https://people.eecs.berkeley.edu/~necula/autded/lecture15-tactics.pdf](https://people.eecs.berkeley.edu/~necula/autded/lecture15-tactics.pdf)







View patterns might be a way of getting something like the Agda .x syntax, where something is forced to be something by unification?







[https://gitlab.haskell.org/ghc/ghc/wikis/view-patterns#Relatedwork](https://gitlab.haskell.org/ghc/ghc/wikis/view-patterns#Relatedwork)







Kmett mentions a "octagonal" domain. What the hell is he talkiing about. He also moentions interval and polyhedral which makes more sense







https://www-apr.lip6.fr/~mine/publi/article-mine-HOSC06.pdf







Huh. Interesting. It is in between power of polyhedral and interval. allows sums/differences of two variables. I think I've heard this called difference logic. This paper also mentions galois connections. Galois connections are studied in the context of abstract interpetation?







https://arxiv.org/pdf/1807.08711.pdf 







Using Agda and galois connections. Interestign example of sets of even and odd numbers.







This other paper does an interesting thing of defining division in terms of a glaois connection. Might we also get a good definition of fractions that way? a fraction t ~ m/n is a "number" such that forall z. x <= y   -> x * t * n <= y * m?  There is an notion of negative numbers, fractions, etc as reified weirdo operations that can't be solved yet. Hmm. Yeah, This jives with galois theory doesn't it. That book I was reading was talking about field extensions. Or number systems being invented to make more equations solvable. The reals make ? solvable. fractions make division solvable. Complex makes roots solvable. finite field extensions make simple algerbaic equations solvable. 







[https://www.sciencedirect.com/science/article/pii/S1567832612000525](https://www.sciencedirect.com/science/article/pii/S1567832612000525)







Oliveira, that same guy as the Search monad and some other thingds







I suppose perhaps there is something similar happening in functional programming. to make recrsuively defined functions solvable, you need to extemnd the language with a Y-combinator or some of fixed point operator.







Interval airthemteic in a theorem prover. That is a way of getting sets. Min and Max. Interesting







This is also a pleasant by Backhouse







http://www.cs.nott.ac.uk/~psarb2/G53PAL/FPandGC.pdf







indirect equality







m=n ===  forall k. k <= m <=> k <= n













Galois connection between convex hulls of integer points? There is a sequence of abstractions for integer programming. You can turn dimension by dimension into integer so there are 2^D different domains to talk about. And there is this grid of connections that forms a lattice itself? Like the top is the completely R^D, and the bottom is Z^D. Using these connections is the branch and bound procedure. 







Floor and Ceil are also galois connections. Maybe also round? I had been thinking in terms of ibjects being individual numbers, not convex sets of numbers. Convex sets does tie in much better to categorical thinking







http://www.cs.tau.ac.il/~msagiv/courses/asv/absint-1.pdf







An interesting paper tutorial on galois connections. V cool.







monotone functions between are like natural tranfromations?







One place used dup as the adjunction to max.







There may be more to galois connections than adjunctions, since they are assuming a meet and join operation. Some interesting doncturctions like the porduct of galois connections.







[https://www.youtube.com/watch?v=KxeHGcbh-4c](https://www.youtube.com/watch?v=KxeHGcbh-4c)  








minikanren is strongly unification based. it is using search for the unification map. In simplest form [UniMap]







[https://github.com/JeffreyBenjaminBrown/learn-logict](https://github.com/JeffreyBenjaminBrown/learn-logict)








https://www.msully.net/blog/2015/02/26/microkanren-%CE%BCkanren-in-haskell/








[https://gup.ub.gu.se/file/207634](https://gup.ub.gu.se/file/207634) logic typed variable claesson







[http://dev.stephendiehl.com/fun/006_hindley_milner.html#unification](http://dev.stephendiehl.com/fun/006_hindley_milner.html#unification) unification.







[http://webyrd.net/arithm/arithm.pdf](http://webyrd.net/arithm/arithm.pdf)







[https://ro-che.info/articles/2017-06-17-generic-unification](https://ro-che.info/articles/2017-06-17-generic-unification) unification-fd . 







[https://winterkoninkje.dreamwidth.org/100478.html](https://winterkoninkje.dreamwidth.org/100478.html)







unification-fd inserts itself in the same position Fix does.







Lattices. Subsumption lattice for unufication. More and less general partial order. meet and join. top and bottom







## Notes from 2017 -Resolution and unification







So I was learning about about minikanren. There are some videos online. Minikanren is a logic programming language (like Prolog) that embeds easily into other languages because it has a small core.







Logic programming is weird mainly (partially) because you define relations rather than functions. Relations do not have a input output relationship like functions do. In a sense they are like functions where you get to choose which thing is output and which things are input. Pretty crazy.







The most obvious way to do this to me is to make every function a bag of functions. Just write one function for every possible choice of output variable. These functions may need to be non-deterministic, outputting multiple possibilities, for example for y = x^2 gives x = +sqrt(y) or -sqrt(y). However, this isn't really how logic programs are written. Instead they deduce how to use a relation as a function.







I find most intro to prolog stuff off putting, talking about socrates(man), when that is not a problem I have ever given a crap about.







Resolution is the classical logic version of function composition.







a-> b and b->c can be combined easily into a function a-> c.







Implication in classical logic is weird. It translates to







a->b  ====> (not a)  or b







When a is true, b has to be true. When a is false, b can be true or false.







For the statement a implies b to be true then it needs to evaluate to false only when a is true and b is false







not  (a and (not b))







using De Morgan's law you can distribute nots turning ands into ors.







Then that becomes







(not a) or b.







If you have







((not a) or b) and ((not b) or c)







it does not matter what b is really because either b or not b will be false







so this is equivalent to







(not a) or c







since at least one has to be true to make the whole expression true







Unification







Predicate logic allows propositions to depend on variables. Think Prolog.







A simple question given two expressions is whether there are values of the variables that make the expressions equal.







I do this in my head sometimes when I'm looking a a parametric haskell type.







The type variables need to be matched up with two different expressions.







Sometimes this can be too hard to do in my head, especially when the type variables end up being functions.  So there is need for an algorithmic procedure. I mean, also because you want a computer to do it.







First off, let's suppose we have the two expressions in tree form.







Nodes can be Or, And, Predicates, Not.







We'll want them in some canonical form too so that we don't get tripped up by the commutativity or distributivity of Boolean operators







We need to collect up a bucket of deduced equivalences as we go down the trees of the two expressions. Whenever we hit a variable, we check if we have a substitution in our bucket. If so, replace it. If not, we put into our equivalences that variable is equal to whatever the other expression has in that place. When we hit something that trips us up, we announce failure and the expressions couldn't be unified.







The prolog algorithm is roughly guess a pair of terms in the goal (the executing state) and knowledge base (the code base) that will unify. Try to unify them. If they do, then use resolution to get rid of those terms.







Like what if we reflected into Eisenberg's Stitch? Or what was Weirich's thing? People have been talking about intrinsically typed system-F lately.



