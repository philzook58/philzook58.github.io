
There is a collection of ideas that I sprayed at graham and Caleb last week that i haven't written about.

A long whiles back, in dicussions with Metatheory.jl and Catlab.jl, a lot of people were of the opinion that the appropriate data structure for catogerical rewriting should be instrinsically graph-like. The relatively "boring' methodology of braking up a string diagram into terms and recovering the various notions of associativity and commutativty intrinsic to the graphical notation feels off.

The thing is, it is not obvious how to support "graph-like" ness in the egraph.

egraphs as common presented are intrinsically about terms/trees IMO. The "graph" part of the egraph comes from loopy self referential equations between terms like `a = 0 + a` (not a weird equation at all) or `stream_zero = cons(0, stream_zero)` (a bit more exotic).
This appears to be an issue in attempting to straightforwadly move graph like compiler IRs into a egraph based compiler IR.

Supposing we had a good solution to this "graphy egraph" problem, we would also possibly have solutions to the AC, alpha equivalence and scope problems.

In a previous blog post, I commented that the ideas of relational egraphs querying directly apply to graphs of AC terms <https://www.philipzucker.com/relational-ac-matching/> . Associative Commutitativy matching is usually an annoying search process because if you do it top-down, you need to guess how to partition the children of an AC-node. This is not incredibly conceptually or mechanically distinct from how e-matching needs to search for which of the equivalence possible choices to search down.  The most typically encountered notion of graph is one vertices where the edges do not have an intrinsic ordering. A set of edges, where an edge is a pair of vertices. One can add in some extra spice. Ordering of the edges coming out of a vertex is what we expect in typical syntax trees, and trees are indeed a subset of graph.

So what do people do when they try to model things that really have graph-y character in egraphs? Well they tree-ify it somehow.
Categorical string diagrams have a canonical modelling methodology. You can have combinators like horizontal compose, vertical compose, swap, braid , etc. using these combinators you can select on of many possible expressions that represent the string diagram.
For lambda terms, we perhaps use de bruijn indices in some way (you can easily represent graphs by trees if you just cut any backedge with a named indirection), or SKI-like combinators, or defunctionalization, or you can tree-ify with co-de-bruijn variable maps (like in hash cons modulo alpha). They are all messy in their own ways and I have grown pessimistic that a satisfying, comprehensible, efficiently implementable solution exists here. Extract, eval, reinsert is ok (and a good generic strategy for many theories like constant eval, confluent terminating rewrite systems, etc), but my gut says something is a little unsatisfyingly inexpressive there.

So what is the conceptual point of an egraph? I think that it is a structure to maximize upward and downward sharing in terms.
The naive way to perform a term rewriting search it to maintain a database of complete terms. Find you pattern in them and then make a completely new copy of the term with the pattern replaced. This is not very efficient. "Obviously" in `?x + ?y -> ?y + ?x` we don't need to rebuild `x` and `y`, we can just use refences to the old terms of the lhs. Hash consing achieves perfect subsharing in the way.
What the eclass indirection enables is sharing up.  If I set `one + one = two` inside the expression,`f(f(f(f(f(f(f(f(one + one))))))))` using hash consing I have to completely rebuild the `f` chain. The eclass enables a choice point inside there, so all the parent structure of the `f` chain can be shared between the two.

I kind of prefer getting some proof of concept to post about but I'm not making good progress. Blog posts can be anything

# Blah

- FM paritioning
- decompositions of graphs
- draw some pictures of alpha and AC and lambda

References
hash cons modulo alpha
New hash cons alpha
caleb graph hashing
graph rewriting
greta ITGP
chyp

notions of equality
