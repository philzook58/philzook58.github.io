
Egraphs are a data structure for useful for equational reasoning and optimization.

The success of Satisfiability Modulo Theories and the expressivity it offers in terms of built in theories leads one to wonder how to bake in reasoning. Indeed the
Equality saturation as used by egg is not a backtracking search.

There exist many specialized algorithms for dealing with sets, multisets, linear expressions and polynomials.

The motivating schematic equations is EMT = SMT - SAT.

# Constraints via sidecar SMT

A first technique is to mirror all the equalities learned into a side car SMT solver.

The utility of this is to enable SMT queries, specifically in guards of equality saturation rules. Guards are distinguished from multipatterns in that no new pattern variables may be bound in them.

SMT solvers support the generation of new constants and can have learned equalities asserted into them.

This technique has analogs in the form of Constraint Logic Programming or Constrained Horn Clauses, or constrained rewriting.

If one has a has a backtrackable egraph implementation, one may choose to treat some constraints lazily, taking on the optimistic constraint until it is proven contradictory. This technique can be viewed as synthesizing a set of constraints sufficient to achieve.

Example:

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

Linear equations can be put into row echelon form. The row echelon form can be used to canonically quotient a vector space by a subspace.

Ground multiset equations are completeable {a,b,b} = {c,d}.

Grobner bases

Ground terms equations. In an amusing self reflection, the theory solver could itself be an egraph, which is a canonizer for ground term equations. It is unclear why this would be useful. One could separate functions symbols to those considered outer and inner. This would enable for example, two egraph implementations to interact with each other.

It is possible to use theory solvers that may not terminate. One may either hope they do, or terminate their completion process early and accept the incomplete canonizers.

String Rewriting. The completion of string rewriting in general will not complete because string rewriting is rich enough to encode turning complete computation, and successful completion would give a decision procedure for . This is an important counterexample as string rewriting can be viewed as ground equations + associativity. Because of this, a fully satisfying solution to an egraph (whjich represent ground equations) with baked in associativity is unlikely to be possible.

Knuth Bendix Completion - One may choose eids to be so structured as to be terms themselves. Unorientable derived equations can be lifted to be equality saturation rules. This is related to ordered completion/rewriting.

Other examples of egraph extensioins that are evocative of the structured eid idea are colored egraphs which tag eids with a notion of context and slotted egraphs which tag eids with alpha invariant variables.

An egraph is a bipartite graph of eclasses and enodes. When performing design space exploration on a structure like this, it can be difficult to know when to assign

bottom up ematching
the egraph is equations and a term bank
