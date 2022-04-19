

# Union Finds

# Proof Production
[Proof producing congruence closure](https://www.cs.upc.edu/~roberto/papers/rta05.pdf)
A union find is a data structure useful for finding connected components in a graph. The "proof" that two vertices are connected is the path between them. We need to maintain an incremental spanning tree of some kind.


Is ematching a wam? I suppose so. Ematching over a fixed egraph is easily expressible in prolog.
We could implement egraph as `assert`
We can't use unification vars?
Does tabling help?
```
f(1,2,3).
g(1,2,3).

-? plus(A,B,AB), plus(AB,C,ABC)
```