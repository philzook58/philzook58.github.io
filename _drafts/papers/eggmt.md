# Omelets Need Onions : Approaches To Egraphs Modulo Theories

Egraphs are a generic data structure for equational reasoning and optimization. It is possible to encode reasoning about familiar mathematical objects into this framework. For example, one of the benefits of egraph rewriting is that it can handle commutative and associative operations like addition and multiplication. These identities are difficult to orient once and for all as some optimizations are only unlocked once the appropriate terms have bubbled together. However, using these generic mechanisms is more expensive than bespoke routines. There exist many specialized algorithms for dealing with sets, multisets, linear expressions and polynomials.
 It is also possible to encode Gaussian elimination into egraph rewrite rules, at extreme overhead compared to a custom implementation. A natural question arises: How can one bake in these special mechanisms while retaining the generality and flexibility of the egraph?

Destructive rewrite rules

# Constraints via sidecar SMT

EMT = SMT - SAT

The success of Satisfiability Modulo Theories and the expressivity it offers in terms of built in theories leads one to wonder how to bake in reasoning. Indeed the
Equality saturation as used by egg is not a backtracking search.

The motivating schematic equations is EMT = SMT - SAT.

A prominent useful class of automated reasoning solvers are Satisfiability Modulo Theories solvers. A SAT solver and an egraph are communication fabric by which theory specific solvers talk to each other. Nelson-Oppen Combinations and the Shostak procedure. An emphasis in SMT is on the SAT solver which has a backtracking flavor whereas egraph rewriting has a saturation flavor.

In principle, an SMT solver with the SAT solver removed or unused is a form of

The e-matching d the emtachhing algorithms are syntactic and furthermore CVC5 and Z3 do not necessarily make theory specific operators like integer addition available to the ematcher.
Alt-ergo is an exception.

A first technique is to mirror all the equalities learned into a side car SMT solver.

The utility of this is to enable SMT queries, specifically in guards of equality saturation rules. Guards are distinguished from multipatterns in that no new pattern variables may be bound in them.

SMT solvers support the generation of new constants and can have learned equalities asserted into them.

This technique has analogs in the form of Constraint Logic Programming or Constrained Horn Clauses, or constrained rewriting.

If one has a has a backtrackable egraph implementation, one may choose to treat some constraints lazily, taking on the optimistic constraint until it is proven contradictory. This technique can be viewed as synthesizing a set of constraints sufficient to achieve.

Example:

Two designs for dealing with constraints are either eaergly discharge the constraint obligation before asserting the rule or the allow the rule to fire but note the equality as happening under as lazily discharged constraint. The latter requires a notion of context.

# Extract and Simplify

Another technique is to extract terms from the egraph, simplify them using bespoke routines, and then assert the equality.

Whereas the inidividual rules manipulating de Bruijn indices, or assocaitgivty and commutativity would lead to perhaps undesirble administrative junk in the egraph, this technique enables big leaps to be taken.

On the downside, there intermediate steps are sometimes not actually junk and enable rewrites.

# Containers and Generalized Enodes

Egraphs systems are the interplay of two entities, enodes and classes. A natural approach to generalize egraph is to consider generalizing one or both.

The most standard notion of enodes is a function symbol combined with a fixed number of ordered children.

In the egg rust library, a generic notion of enode is enabled by the use of the Language trait. This trait requires the construtors of possible enodes to be distinguishable, teh children enumerable. The capaibiulities are necessary to canpnized and ematch through the enode.

Enodes can be generalize such that their children eids are held in different data structures.
If enodes hold their children in vectors this supports Associativity to some degree, multisets support AC, and sets support ACI.

Many of the design ideas and issues appear also in the context of pure terms or hash conses. Enodes are basically the same thing a nodes of a term. Eids are to same thing as the unique identifiers of a hashcons, just with extra equality capability.

Some egraph systems support primitive types such as 64 bit integers or concrete strings. Another primitive type that can be supported is Vectors

# Generalized Union Finds and Structured / Semantic Eids

The purpose of the union find is quickly canonize eclass ids. The union find can be seen as a normal form or canonizer of a system of atomic equations. Indeed, the knuth bendix completion of a ground atomic equational theory is guaranteed to terminate and the resulting rewrite system can be interpreted as a union find.

A union find can be built that carries group elements on it's edges. In this manner it can be used to store an equivalence relation modulo a group action. relations like `6 + x = 3 + y` . Another way of looking at it is atomic ground completion modulo a group action.

- Linear equations can be put into row echelon form. The row echelon form can be used to canonically quotient a vector space by a subspace.

- Ground multiset equations are completeable {a,b,b} = {c,d}.

- Grobner bases

- Ground terms equations. In an amusing self reflection, the theory solver could itself be an egraph, which is a canonizer for ground term equations. It is unclear why this would be useful. One could separate functions symbols to those considered outer and inner. This would enable for example, two egraph implementations to interact with each other.

- Group action. Slotted egraphs

It is possible to use theory solvers that may not terminate. One may either hope they do, or terminate their completion process early and accept the incomplete canonizers.

- String Rewriting. The completion of string rewriting in general will not complete because string rewriting is rich enough to encode turning complete computation, and successful completion would give a decision procedure for . This is an important counterexample as string rewriting can be viewed as ground equations + associativity. Because of this, a fully satisfying solution to an egraph (whjich represent ground equations) with baked in associativity is unlikely to be possible. Sequence egraphs

- Knuth Bendix Completion - One may choose eids to be so structured as to be terms themselves. Unorientable derived equations can be lifted to be equality saturation rules. This is related to ordered completion/rewriting.

Other examples of egraph extensioins that are evocative of the structured eid idea are colored egraphs which tag eids with a notion of context and slotted egraphs which tag eids with alpha invariant variables.

An egraph is a bipartite graph of eclasses and enodes. When performing design space exploration on a structure like this, it can be difficult to know when to assign

Colored egraphs attach a notion of context to each equality.

## What patterns are possible?

Equational theories fall into different classes of how many solutions they may allow for their E-unification or E-matching problems.
Some theories will only have a finite set of solutions, some a countably infinite set, and others an uncountably infinite set.

Pattern matching and unification are equation solving. The problems are formulated as goal equations to be solved, and the solutions are substitutions

- `{?x , ?y} ?= {1, 2, 2}`
- `?x \cup ?y`
- `?x + ?y`

What solutions does `?x + ?y =? 42`.   `{ [?x |-> 42 - n, ?y |-> 42 + n] | n \in \bN}` This cannot be finitely solved as substitutions.

`?x + ?y = 42, ?x = 16` this is uniquely solvable.

## Bottom Up EMatching

A different formulation of the pattern matching problem that solves the issues of top down matching is the bottom up matching procedure
Given a termbank T and a pattern p, find substituions {v |-> t | t \in T} such that  

A reason that top down matching may feel natural is that makes sense for a pointer chasing implementation of terms. One can infer a termbank from `t` in

the egraph is equations and a term bank

## Completeness: Should One Care?

Naive equality saturation is not a complete equational theorem proving method. The main interest in understand the completeness of an EMT method relative to the naive algorithm not because the naive algorithm has good theoretical properties. it is that naive equality saturation is simple to explain, pragmatic, and efficient. Alternate EMT methods may have greater or less reasoning power than the naive algorithm on different problems. If the method is equally simple and more efficient that is fine.

Completeness is useful if you want absolute guanrantees you have the minimum possible term or that if the saturation saturates there is no solution.

Soundness however _is_ table stakes.

# Background on Rewriting Modulo Theories
