

# Union Finds
## Reference union finds
## Union find arrays and ints
What is a pointer but an index? What is an index but a pointer?

# E-matching
Simplify
[de Moura and Bjorner](https://leodemoura.github.io/files/ematching.pdf)
Their VM is quire similar to WAM. 


# Proof Production
[Proof producing congruence closure](https://www.cs.upc.edu/~roberto/papers/rta05.pdf)
A union find is a data structure useful for finding connected components in a graph. The "proof" that two vertices are connected is the path between them. We need to maintain an incremental spanning tree of some kind.


# PEG

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

YOGO koppel
[Sketch-Guided Equality Saturation Scaling Equality Saturation to Complex Optimizations in Languages with Bindings](https://arxiv.org/pdf/2111.13040.pdf) de buijn indexes with extraction. Rise compiler
