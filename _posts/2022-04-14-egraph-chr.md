---
date: 2022-04-14
layout: post
title: "Embedding E-graph Rewriting and Egglog in Constraint Handling Rules"
tags: prolog chr egraph
description: I embed e-graph rwriting into SWI prolog constraint handling rules
---

Pretty stoked about this!

E-graph rewriting is all the rage. You may have encountered the famed [egg](https://egraphs-good.github.io/), the rust e-graph library.

E-graphs are a compact representation of terms related through equality. It does this by both sharing subterms, but also sharing parents of terms in a sense through the eclass indirection. It is something like a [hashcons mixed with a union find](https://www.philipzucker.com/egraph-1/). In the equality saturation approach to rewriting, you don't destructive rewrite your terms, instead you store all the equalities you learn in the egraph. This was you don't have to worry about rewriting yourself into a corner, you just have to worry about running out of memory.

I've made a couple posts about embedding egraph rewriting in souffle datalog 
 - [Naive E-graph Rewriting in Souffle Datalog](https://www.philipzucker.com/datalog-egraph-deux/)
 - [A Questionable Idea: Hacking findParent into Souffle with User Defined Functors](https://www.philipzucker.com/datalog-egraph-deux/)

Way back in August when I was talking about [egglog](http://www.philipzucker.com/egglog/), a type of datalog built on top of egg, [Jose Morales](https://twitter.com/notjfmc/status/1422215450675535877?s=20&amp;t=RyHMtBS3ySaALLC9MuGmUA) asked about the relationship to Constraint Handling Rules (CHR). I had basically no idea what CHR was, so I looked it up and gave a weak negative answer. However, he was right. It turns out it is quite easy to embed egraph rewriting into CHR. [Yihong](https://github.com/yihozhang/cchr/blob/master/experiment/egraph.cchr) I think had also twigged onto this notion at a point.

Constraint handling rules are a multiset rewriting language. You can perform both destructive and non destructive rewriting. Nondestructive Propagation rules look like `foo, biz ==> bar.`, destructive rules like `foo, biz <=> bar` and a rule that removes biz but keeps foo is `foo \ biz <=> bar`. For more on CHR, see the [CHR book](http://www.informatik.uni-ulm.de/pm/fileadmin/pm/home/fruehwirth/constraint-handling-rules-book.html), the very friendly [Anne Ogborn's tutorials](https://github.com/Anniepoo/swiplchrtut/blob/master/basics.adoc), the [ICLP tutorial](https://dtai.cs.kuleuven.be/CHR/files/tutorial_iclp2008.pdf), and the [SWI prolog docs](https://www.swi-prolog.org/pldoc/man?section=chr).

A common idiom in CHR is to turn on "set semantics" by making an explicit rule to delete duplicates `foo \ foo <=> true.`. In this case `==>` becomes basically the same as datalog's `:-`. Vice versa, you can encode some destructive CHR rewriting rules in datalog if you have subsumption or lattices. The two systems are rather similar. Hence it makes sense that if one can encode egglog/egraphs into souffle, one can also encode them into CHR.

The basic encoding is extremely related to the one that can be found in chapter 6 of the [CHR book](http://www.informatik.uni-ulm.de/pm/fileadmin/pm/home/fruehwirth/constraint-handling-rules-book.html) for embedding term rewriting. In fact it's so similar it isn't clear that maybe this is what the book is getting at?

I define a constraint `eclass/2` that relates an enode to it's eclass id. Eclass ids I can represent using prolog unification variables, since these are already a union find. We put ground terms into the egraph by flattening them into their eclass costraints. For example `f(f(a))` gets expanded to `eclass(a,A), eclass(f(A), FA), eclass(f(FA), FFA)`

The congruence rule is very simple. It is related to the "set semantics" rules above, but also to a hash consing transformation mentioned in the book

```prolog
:- use_module(library(chr)).
:- chr_constraint eclass/2.
congruence @ eclass(T, E1) \ eclass(T, E2) <=> E1 = E2.
```

This rule on it's own is sufficient to normalize the egraph. How crazy is that. The e-graph is 1 line of code basically!

We can try it out on the `f(f(a)) = a` example that I use as my zeroth order egraph sanity check. Once you assert that equality, no matter how many fs you apply, `ffffffff(a)` always reduces down also to either `f(a)` or `a`.

One of the things that I think makes this embedding so nice, is that CHR is typically embedded in prolog, so I can do a little metaprograming in prolog to ease the burden. In this case, I can do the ground term flattening into the egraph using some prolog term destructuring code `insert`.

```prolog
:- use_module(library(chr)).
:- chr_constraint eclass/2.
congruence @ eclass(T, E1) \ eclass(T, E2) <=> E1 = E2.

:- initialization(main,main).

% helper to insert ground terms into egraph
insert( T , E) :-
 ground(T),
 var(E),
 T =.. [F | Args],
 length(Args, N), length(Es, N),
 T2 =.. [F | Es],
 eclass(T2, E),
 maplist(insert, Args, Es).


main(_) :-  insert(f(f(a)), FFA), insert(a, A), FFA = A,  insert(f(f(f(f(a)))), _FFFFA),
            chr_show_store(true).
/*
Output:
eclass(a,_62922)
eclass(f(_62922),_62808)
eclass(f(_62808),_62922)
*/
```

We see here we end up with 2 eclasses and 3 enodes. This is correct.

To embed egraph rewriting was a bit trickier. It turns out CHR has a pretty rigid execution order semantics. It appears that it grabs off the top of th constraint store and applies the rules in order. For egraph rewriting this is a problem. We don't in general expect egraph ewriting to finish. We need to early stop it. In addition, the naive way of doing this was just churning in a loop on the first rules and the top of the constraint store.
 
What I decided to do was batch the rewrites together. Instead of directly writing into `eclass`, instead I generate `eclass2/2` constraints. I then collect these up into a list using `collect/1`. This completes a single ematching run. Then if I want to continue `process` converts this list back into `eclass` constraints that can trigger more rewriting rules firing.


```prolog
:- use_module(library(chr)).
:- initialization(main,main).
:- chr_constraint eclass(?,-), eclass2(?,-), collect/1, kill/0, count/1.

cong @ eclass(T, E1) \ eclass(T, E2) <=> E1 = E2.

% rewrite rules.
comm @ eclass(X + Y, E) ==> eclass2(Y + X, E).
assocl @ eclass(X + YZ, E), eclass(Y + Z, YZ) ==> eclass2(X + Y, XY), eclass2(XY + Z, E).
assocr @ eclass(X + Y, XY), eclass(XY + Z, E) ==> eclass2(X + YZ, E), eclass2(Y + Z, YZ).

% To collect up new eclasses
collect @ eclass2(T,E), collect(L) <=> L = [eclass3(T,E) | L1], collect(L1).
done @ collect(L) <=> L = [].

% helpers to cleanup eclass2
kill @ kill \ eclass2(_,_) <=> true.
killdone @ kill <=> true.

% helper to count eclasses
count @ count(N), eclass(_,_) <=> N1 is N + 1, count(N1).

% Take rhs list and inject them as CHR constraints 
process([]).
process([eclass3(T, E)| L]) :- eclass(T,E), process(L).

% Do N rewriting runs
batch() :- collect(L), process(L).
batch(0).
batch(N) :- batch(), N1 is N -1, batch(N1).

init_add(N) :- eclass(N,E), N1 is N - 1, init_add_aux(N1,E).
init_add_aux(0,_).
init_add_aux(N,E) :-
  eclass(N, EN), eclass(EN + E, E2), N1 is N-1, init_add_aux(N1, E2).


insert( T , E) :-
 ground(T),
 var(E),
 T =.. [F | Args],
 length(Args, N), length(Es, N),
 T2 =.. [F | Es],
 eclass(T2, E),
 maplist(insert, Args, Es).


main(_) :- 
          N = 6,
          init_add(N),
          Num is 3**(N) - 2**(N+1) + 1 + N, print(Num),
          BNum is N,
          time(batch(BNum)), kill, count(0), chr_show_store(true).
/*
Output:
608
% 397,754,165 inferences, 41.712 CPU in 41.732 seconds (100% CPU, 9535677 Lips)
count(608)

N=5 is under a second. Not good scaling.
*/
```

Pretty, pretty, pretty good.

The good news: We have full prolog available at our fingertips. We can express full  [egglog](http://www.philipzucker.com/egglog/) also, we are not constrained to just simple rewrite rules.

The bad news: egg utterly destroys this code in terms of speed. Egg can handle the associative commutative benchmark at 10 nodes in under a second. This CHR embedding stack overflows after a good couple minutes at N = 7 or so.

All of this is so close to the main line of prolog interests, I'd be surprised if this isn't already documented somewhere. But I don't know where. If you have suggestions about how o improve the efficiency of the code or references, please drop me a line!

# Bits and Bobbles

- It'd be good to do some metaprogramming to make it easier to write the rewrite rules. This may require some prolog macros, since I don't think I can call prolog predicates in the pattern of the CHR rule.
- [Elpi](https://github.com/LPCIC/elpi) is a lmabda prolog interpeter that supports CHR. Does this mean we can have egraphs with bound variables?! It also directly integrates to coq.
- [CCHR](https://github.com/nickmain/cchr) is a compiler from CHR to C. I believe it is the fastest implementation around. How good does it do?
- CHR Union Find. I am using prolog variables for my union find, but it may be more efficient to use a CHR union find a la chapter 10 of the CHR book. This would enable me to use grounded terms and possibly much better term indexing. Supposedly indicating the types of the fields of constraints helps speed.
- Go flatter. This might lead to better indexing properties