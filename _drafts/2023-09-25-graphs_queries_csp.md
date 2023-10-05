
SQL queires are enumerating homomorphisms between the query and the database. This perspective puts the query and the database on smilar footing, which feels odd.

As a subcase of this capability, if the database is holding an edge table and attributes, then a query is a graph homomorphism solver.
If we dymmetrically place two graphs into the dtabase and in a query, we can enumerate isomoprhisms. Isn't that fun?

Another perspective is that the query is a formula, and the database is a model of the formula.

We are used to small queries and large databases, but this is not a definition

A perspective on what a constraint satisfaction problem is is that is is a homomorphism problem.
For example, graph coloring is a homomorphism from a graph to a complete graph of colors (with no self edges).

Constraint satisfaction is an assignment to variables values frm their domain subject to constraints. The particular connectivty of a problem can be represented by a hypergraph. The target structure represents the domains the variables can take on, and the constraint hyperedges map to a relation representing the constraint.
A class of CSP problems is allowing the connecvtivity graph to vary, while keeping the target (the types of constraints fixed). Is this a useful characterization? Eh. It's interesting that it ties into other mathemtical topicas.

The naive solution of a constraint satsifaction problem is to just make a big sequence of loops, pruning / breaking with checks that constraint are satisifed. We want to push the checks as high as possible.
This a a very static perspective.
More dynammically, we want to pick the variable ordering inside the choice branches. This is more of a backtracking feel. We do proppagation to disallow subchoices
