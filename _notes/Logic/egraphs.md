---
layout: post
title: E-graphs
---

- [E-Graph](#e-graph)
- [My E-Graph Blog Posts](#my-e-graph-blog-posts)
- [Union Finds](#union-finds)
  - [Reference union finds](#reference-union-finds)
  - [Union find arrays and ints](#union-find-arrays-and-ints)
  - [Variations](#variations)
- [Hash Cons](#hash-cons)
- [E-matching](#e-matching)
- [Equality Saturation](#equality-saturation)
- [Proof Production](#proof-production)
- [Applications](#applications)
- [PEG Program Expression Graphs](#peg-program-expression-graphs)
- [Egglog](#egglog)
- [Misc](#misc)



# E-Graph
What is an e-graph?

What is a summer's day? A rainbow?

E-graphs are a data structure that efficiently holds terms and equalities between terms.

It is useful for algebraic simplification, program transformations and proving equivalences in equational reasoning

Destructive term rewriting can be used in 



# My E-Graph Blog Posts
- [E-graphs in Julia (Part I)](https://www.philipzucker.com/egraph-1/)
- [E-Graph Pattern Matching (Part II)](https://www.philipzucker.com/egraph-2/)
- [Progress on Automated Reasoning for Catlab with Metatheory.jl Egraphs](https://www.philipzucker.com/metatheory-progress/)
- [Rewriting Monoidal Categories in the Browser with Egg](https://www.philipzucker.com/rust-category/)
- [Union Find Dicts: Dictionaries Keyed on Equivalence Classes](https://www.philipzucker.com/union-find-dict/)
- [A Simplified E-graph Implementation](https://www.philipzucker.com/a-simplified-egraph/)
- [Partial Evaluation of a Pattern Matcher for E-graphs](https://www.philipzucker.com/staging-patterns/)
- [Encoding E-graphs to Souffle Datalog](https://www.philipzucker.com/egraph-datalog/)
- [Egglog: a Prolog Syntax for Egg, Checkpoint I](https://www.philipzucker.com/egglog-checkpoint/)
- [JuliaCon 2021 Talk on Metatheory.jl and Snippets From the Cutting Room Floor](https://www.philipzucker.com/juliacon-talk/)
- [Egglog 2: Automatically Proving the Pullback of a Monic is Monic](https://www.philipzucker.com/egglog2-monic/)
- [Egglog Examples: Pullbacks, SKI, Lists, and Arithmetic](https://www.philipzucker.com/egglog-3/)
- [Naive E-graph Rewriting in Souffle Datalog](https://www.philipzucker.com/datalog-egraph-deux/)
- [A Questionable Idea: Hacking findParent into Souffle with User Defined Functors](https://www.philipzucker.com/souffle-functor-hack/)
- [Embedding E-graph Rewriting and Egglog in Constraint Handling Rules](https://www.philipzucker.com/egraph-chr/)


# Union Finds
Union finds are also called disjoint set datastructures.
You can take a set an group it into equivalence classes. One place this is useful is finding the connected components of a graph.

There are different styles of union finds and both make one thing in different and interesting ways.

At a level of fairly high abstraction, a union find is a contracting map. You iterate the map to a fixed point. Each equivalence class is the basin of a fixed point.

See coq post https://www.philipzucker.com/simple-coq-union-find/

How essential is path compression? It is the thing that gets you that inverse ackermann complexity. It requires mutation so far as I know.

[Union find dict](https://www.philipzucker.com/union-find-dict/)

## Reference union finds
A chain of pointers that lead up to a root. Often the root is a pointer to itself.

## Union find arrays and ints
What is a pointer but an index? What is an index but a pointer?
In some sense your ram is just a giant array that you hand out. And vice versa you can build the analog of pointer based algorithms by using an array as ram.

In some languages you don't have access to raw pointers easily. The array style also makes it easier/more natural to copy union finds. This style also makes it more clear how to talk about the union find in a purely functional way.

## Variations
[Union Find Dicts: Dictionaries Keyed on Equivalence Classes](https://www.philipzucker.com/union-find-dict/)

Union find with group elements on edges.

Scoped Union find


# Hash Cons






# E-matching
Searching over the egraph. It is both simple and complex.
It is a brother of pattern matching. The branching factor of each eclass means that it is more nondeterministic than tree pattern matching.
It is similar to database search. Relational E-matching. 

Consider
- pattern matching at the root of a single tree
- pattern matching at ever node in a tree 
- pattern matching over a database of trees (forest)

- pattern matching over a DAG
- pattern matching over a graph (hard in principle (subgraph isomorphism), in practice maybe not that bad)

Simplify
[de Moura and Bjorner](https://leodemoura.github.io/files/ematching.pdf)
Their VM is quire similar to WAM. 


# Equality Saturation

# Proof Production
[Proof producing congruence closure](https://www.cs.upc.edu/~roberto/papers/rta05.pdf)
A union find is a data structure useful for finding connected components in a graph. The "proof" that two vertices are connected is the path between them. We need to maintain an incremental spanning tree of some kind.

We also need to record "reasons" why each edge got added.

# Applications
- Denali https://courses.cs.washington.edu/courses/cse501/15sp/papers/joshi.pdf
- Herbie - improve accuracy of floating point expressions
- [Szalinksi](https://github.com/uwplse/szalinski) shrink 3d cad programs
- [Vectorization for Digital Signal Processors via Equality Saturation](https://asplos-conference.org/abstracts/asplos21-paper142-extended_abstract.pdf)
- [SPORES](https://arxiv.org/abs/2002.07951)


- [High-performance symbolic-numerics via multiple dispatch](https://arxiv.org/abs/2105.03949)
- 
# PEG Program Expression Graphs

<https://ztatlock.net/pubs/2009-popl-equality-saturation-optimizations-egraphs.pdf>
https://rosstate.org/publications/eqsat/

Control flow graph (CFG) is just like, a thing. Its denotational semantics are a bit confused. 

Egraphs like talking about functions. How to encode something cfg like into functions?

Dataflow graphs are basically just a DAG functional representation. So that intra block dataflow is not really a problem.

Being in SSA make one close to purely functional. YOu never assign to the sam name twice (although let binding shadowing could also model this purely functionally).

SSA Phi nodes are slightly bizarre. Gated Phi nodes make explicit the condition on which the merging happens. This makes them more like a purely functional if-then-else.

One can consider using streams as a functional representation of loop behavior. There are operations like tail, head, other on the stream.


PEGs have some clues on how to treat summation symbols  $\Sigma$ in an egraph. Surely you can write a sum function asa CFG. Partial Sums / indefinite integrals rather than closed sum, definite integrals.

Is there a relationship between pegs and timely dataflow?

You only Grep once by koppel - uses PEG-like representation for semantic code search.

[representing loops within egg](https://github.com/egraphs-good/egg/discussions/106)

RVSDG
https://github.com/jameysharp/optir/

Loops in egraphs and Landin's knot.

[Equality Saturation: a New Approach to Optimization](https://cseweb.ucsd.edu/~lerner/papers/popl09.pdf)
# Egglog

# Misc
What would be a mvp egraph in C specialized for the comm/assoc problem look like.
Use reference based union find with tag bits?


Is ematching a wam? I suppose so. Ematching over a fixed egraph is easily expressible in prolog.
We could implement egraph as `assert`
We can't use unification vars?
Does tabling help?
```
f(1,2,3).
g(1,2,3).

-? plus(A,B,AB), plus(AB,C,ABC)
```

l
[Sketch-Guided Equality Saturation Scaling Equality Saturation to Complex Optimizations in Languages with Bindings](https://arxiv.org/pdf/2111.13040.pdf) de buijn indexes with extraction. Rise compiler


[Cheli Thesis](https://arxiv.org/abs/2112.14714)

[EGRAPH 2022 workshop](https://pldi22.sigplan.org/home/egraphs-2022)
[denali](https://courses.cs.washington.edu/courses/cse501/15sp/papers/joshi.pdf)

[Yihong trick to make ematching faster](http://effect.systems/blog/ematch-trick.html)

