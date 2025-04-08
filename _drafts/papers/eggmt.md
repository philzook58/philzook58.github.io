# Omelets Need Onions : Approaches To Egraphs Modulo Theories

Egraphs are a generic data structure for equational reasoning and optimization. One of the benefits of egraph rewriting is that it can handle difficult to orient identities like associativity and commutativity (AC) in a generic way. However, using these generic mechanisms is more expensive than bespoke routines. There exist specialized algorithms and data structures for dealing with sets, multisets, linear expressions, polynomials, and binders. A natural question arises: How can one combine the generic capabilities of egraph rewriting with these specialized theories?

# Extract and Simplify

For some of these theories, it is intuitively clear how we would normalize the term form. Is is the eclass indirection that makes the subject confusing. A simple technique to use the ability to normalize terms, is to replace those normalizing rewrite rules with an extract and simplify stage to the egraph. This allows many directed nornmalizing steps to be taken at once without bloating the egraph with administrative junk.

A downside of this technique is that the intermediate states may not really be junk. For AC, the intermediate states may bubble together or collect up terms in such a way as to unlock

# Constraints via sidecar SMT

A prominent useful class of automated reasoning solvers are Satisfiability Modulo Theories (SMT) solvers. A SAT solver and an egraph are communication fabric by which theory specific solvers talk to each other. The SAT solver leads to SMT having a backtracking flavor whereas egraph rewriting has a saturation flavor. A reasonable approach to Egraphs modulo theories can be found in the schematic equation $EMT = SMT - SAT$. If one only asserts unit clauses to an SMT solver then the SAT solver is not needed.

The core technology of SMT solvers is largely the same, but optimized for different use patterns and the first order model semantics is not the desired one for the purposes of optimization.

Upon satisfiability, SMT returns an arbitrary model. Equality saturation specifically wants a justified or minimal model, one in which every equality is forced by the constraints. As an example, given the problem `a = b` `c = d` an SMT solver may return a universe containing only a single element `{a : v!0, b : v!0, c: v!0, d ; d!0}, identfying everything with eveything.

The e-matching d the emtachhing algorithms are syntactic and furthermore CVC5 and Z3 do not necessarily make theory specific operators like integer addition available to the ematcher.
Alt-ergo is an exception.

Nevertheless, a technique for EMT is to maintain an eqaulity saturating egraph and to mirror all the equalities and theory specific facts into a side car SMT solver. The utility of this is to enable SMT queries, specifically in guards of equality saturation rules. Guards are distinguished from multipatterns in that no new pattern variables may be bound in them.

```
(push)
(assert (not guard))
(check-sat)
(pop)
```

This technique has analogs in the form of Constraint Logic Programming or Constrained Horn Clauses, or constrained rewriting.

# Containers and Generalized Enodes

Egraphs systems are the interplay of two entities, enodes and classes. A natural approach to generalize egraph is to consider generalizing one or both.

Many of the design ideas and issues appear also in the context of pure terms or hash conses. Enodes are basically the same thing a nodes of a term. Eids are to same thing as the unique identifiers of a hashcons, just with extra equality capability.

Enodes are the data of a model corresponding to function symbols and the eids are the values of the model. The standard simple eid is an integer of some kind, but the fact they are integers are irrelvant. They are uninterpreted entitites whose only property is that they can be compared for equality.

Off by One design problems. Edges and vertices. Material flux is most naturally associated with the faces of cells, not the volumes or vertices. One can mush the different pieces around, wherver there is an enode there is an eclass nearby. A goal is to get the right conceptual picture and the hopefully things will lock into place. This is conceptual advance, and kind of is the only way to advance from our ancestors.

The most standard notion of enodes is a function symbol combined with a fixed number of ordered children.

Enodes can be generalize such that their children eids are held in different data structures.
If enodes hold their children in vectors this supports Associativity to some degree, multisets support AC, and sets support ACI.

In the egg rust library, a generic notion of enode is enabled by the use of the Language trait. This trait requires the constructors of possible enodes to be distinguishable, teh children enumerable. The capaibiulities are necessary to canpnized and ematch through the enode.

The `fn children(&self) -> &[Id];` This can be generalized into `fn children(&self) -> Vec<Vec<Id>>;`

Some egraph systems support primitive types such as 64 bit integers or concrete strings. Another primitive type that can be supported is Vectors

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

An egraph rewriting system may want to mix and match these possibilities. The most straightforward design is to associate a theory with each sort. The sort object is responsible for canonization and maintaining to normalizer data structures. It is not always the case that it makes sense to have one privileged notion of AC for example per sort.

## Completeness: Should One Care?

Naive equality saturation is not a complete equational theorem proving method. The main interest in understand the completeness of an EMT method relative to the naive algorithm not because the naive algorithm has good theoretical properties. it is that naive equality saturation is simple to explain, pragmatic, and efficient. Alternate EMT methods may have greater or less reasoning power than the naive algorithm on different problems. If the method is equally simple and more efficient that is fine.

Completeness is useful if you want absolute guanrantees you have the minimum possible term or that if the saturation saturates there is no solution.

Soundness however _is_ table stakes.

# Background on Rewriting Modulo Theories

E/R

Normalizing completion
