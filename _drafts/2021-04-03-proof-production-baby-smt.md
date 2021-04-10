


I would love to have E-graphs explain how they figured out their equalities in a way i can understand. It would give me peace of mind that it is actually working right, plus it is a genuinely useful service in it's own right.

There's a classic paper about this "Proof producing Congruence Closure" by _
I have had a tough time understanding this paper. It feels like I had to reinvent some things on my own to understand what they are getting at.

A simpler intermediary problem is considering a "proof producing" union-find data structure. What does that mean?

There is a graph interpetation of what union-find is doing. It it finding the connected components of an undirected graph. <https://en.wikipedia.org/wiki/Component_(graph_theory)> The elements of the union find are the vertices, and for every edge in the graph we assert the `union!` of those two vertices. Connectivity in a graph is an equivalence relation because it is reflexive `conn(x,x)`, transitive, and symmettric.

Proof objects or proof certificates are data structures that have enough breadcrumbs that it is easier to verify the certificate than reprove the problem from scratch. There is a spectrum of how much detail you leave out. Really, at the extreme end, you can leave out all the information and just ask the verifier to reprove the problem. At the other extreme, you can include every possible ridiculously tiny step, every bit that flipped in your CPU or what you ate that day.

Connectivity in a graph is such a simple and poly-time solvable problem that proof object is a little loose. But there are two reasonable answers.

1. A set of edges that contains a path between the vertices.
2. an ordered path between the two connected vertices.

It is nice if this set or path is as small as possible for ease of verification and clarity. 

In the context of SMT solving, the smaller the proof, the more generalizable it is and more of the SAT search space is pruned out.

So from the get go, assuming our problem is of a manageable size, we can use standard shortest path algorithms to get a "proof object" of connectivity.

However, we aim to talk about term rewriting, where the graph of all terms you can rewrite to is quite large or infinite. We also are intending on using the technique of egraphs, which are an indirect representation of a collection of vertices of the rewriting graph.

The union find is also online?

From the perspective of union-find as solving a system of equations, each left and right hand side is a vertex and each equation is an edge. A proof is the subset of equations necessary to prove the thing or a specific rewriting path to get from the lhs term to the rhs term.


It is a general purpose principle that if a program is figuring something out or proving something and outputs "yes", a good place to look for a proof object is a trace of the programs execution. This is true for example in prolog, branch and bound solvers, SAT solvers <<https://www.cs.utexas.edu/~marijn/drat-trim/> (drat is basically a SAT solver trace) and other things. 

So we need to instrument our union-find data structure with some extra logging information.

