---
layout: post
title: Discrete Mathematics
---

- [Graphs](#graphs)
  - [Graph Families / Classes](#graph-families--classes)
  - [Minors](#minors)
    - [Cut](#cut)
    - [Flow](#flow)
  - [Decomposition](#decomposition)
  - [Algebra](#algebra)
  - [Logic](#logic)
  - [](#)
  - [Problems](#problems)
    - [Easy](#easy)
    - [Enumeration](#enumeration)
    - [Hamiltonian cycles](#hamiltonian-cycles)
    - [Clique](#clique)
    - [Coloring](#coloring)
    - [Covering](#covering)
    - [Isomorphism](#isomorphism)
    - [subgraph isomorphgism](#subgraph-isomorphgism)
    - [Pfaffian orientation](#pfaffian-orientation)
    - [Matchings](#matchings)
  - [Graph rewriting](#graph-rewriting)
  - [Misc](#misc)
- [Knots](#knots)
- [Matroids](#matroids)
- [Packings](#packings)
- [Combinatorics](#combinatorics)
- [Ramsey Theory](#ramsey-theory)
- [Logic](#logic-1)
- [Set theory](#set-theory)
- [Order Theory](#order-theory)
  - [Lattice](#lattice)







<https://en.wikipedia.org/wiki/Discrete_mathematics>


# Graphs
<https://en.wikipedia.org/wiki/Graph_theory>

[introduction to graph theory - grinberg](https://arxiv.org/abs/2308.04512)
Infinite graphs? How does this even make sense.

[graph theory vids](https://www.youtube.com/playlist?list=PLVqjIisMyo_9h78itHVS2hZzkthxFHoT7)

https://en.wikipedia.org/wiki/Line_graph

https://en.wikipedia.org/wiki/Strongly_connected_component#Definitions Condensation graph - strongly connected component collapsed to vertex

https://en.wikipedia.org/wiki/List_of_graphs particular graphs


https://en.wikipedia.org/wiki/Multigraph multiple edges between vertices
https://en.wikipedia.org/wiki/Directed_graph directed edges
https://en.wikipedia.org/wiki/Rooted_graph graph with distinguished root. "flow graphs". Aczel's anti foundation axiom
https://en.wikipedia.org/wiki/Directed_acyclic_graph
https://en.wikipedia.org/wiki/Graph_labeling

https://en.wikipedia.org/wiki/Hypergraph edges connect more than one vertex

## Graph Families / Classes
<https://en.wikipedia.org/wiki/Category:Graph_families>

https://en.wikipedia.org/wiki/Complete_graph totally connected

https://en.wikipedia.org/wiki/Regular_graph Every vertex has same number of neighbors

https://en.wikipedia.org/wiki/Perfect_graph

https://en.wikipedia.org/wiki/Chordal_graph all cycles of 4 or more vertices have a chord

series parallel graph

https://en.wikipedia.org/wiki/Bipartite_graph separated into two sets of vertices that are not connected. Two colorable.
Tree's are bartite. Even cycle graphs
Konig's theorem - minimum vertex cover = maximum edge cover

https://en.wikipedia.org/wiki/Planar_graph
https://en.wikipedia.org/wiki/Circle_packing_theorem


https://en.wikipedia.org/wiki/Intersection_graph all graphs are intersection graphs. Intersections of sets

https://en.wikipedia.org/wiki/Interval_graph intersection graph of a set of intervals

https://en.wikipedia.org/wiki/Comparability_graph things that are comparable in a partial order have an edge. Total order has complete comparaibility graph. Comparability graphs are perfect




## Minors


Algebraic Graph theory
Graph expanders

### Cut
https://en.wikipedia.org/wiki/Cut_(graph_theory) a

https://en.wikipedia.org/wiki/Bridge_(graph_theory) an edge who's removal increases number of connected components
Tarjan bridge finding algo
Chain decomposition

### Flow 
https://en.wikipedia.org/wiki/Flow_network

https://en.wikipedia.org/wiki/Maximum_flow_problem

[max flow min cut](https://en.wikipedia.org/wiki/Max-flow_min-cut_theorem)

Max cut
## Decomposition
 tree decompoaitions
 <https://en.wikipedia.org/wiki/Tree_decomposition>
There was also the kleene algebra variation of 

https://en.wikipedia.org/wiki/Modular_decomposition


## Algebra
https://en.wikipedia.org/wiki/Adjacency_matrix
https://en.wikipedia.org/wiki/Spectral_graph_theory
cheeger constant. cheeger inequality

Positive and negative value on eigenvectors are a way of labelling or cutting graph.


https://en.wikipedia.org/wiki/Expander_graph sparse graph with strong connectivity properties. hard to cut apart.

[Miracles of algerbaic graph theory](https://www.youtube.com/watch?v=CDMQR422LGM&t=6s&ab_channel=JointMathematicsMeetings)
## Logic
Monadic second order logic.
Existential second of logic let's you talk about selection sets of certaain kinds. Model checking these formulas requires solving dificult NP problems. Many of the problems below fall into this class.

Courcelle's theorem

##
SDP
Max cut approximation

Sherali Adams



## Problems
### Easy
Topological sort
reachability
shortest path
minimum spanning tree
[max flow min cut](https://en.wikipedia.org/wiki/Max-flow_min-cut_theorem) . A corolary on linear duality.


Many (all?) of the easy problems are reducible simply to a linear program.
### Enumeration

https://en.wikipedia.org/wiki/BEST_theorem 

### Hamiltonian cycles
<https://en.wikipedia.org/wiki/Hamiltonian_path>
Visit each vertex once.
Travellign salesman problem is weighted relative

https://en.wikipedia.org/wiki/Eulerian_path visit every edge exactly once

### Clique
https://en.wikipedia.org/wiki/Clique_problem
Find maximal completely connected cluster (clique)

Ramsey theory guarantees clique exists 
### Coloring
<https://en.wikipedia.org/wiki/Graph_coloring>
Register allocation

https://en.wikipedia.org/wiki/Edge_coloring
chormatic index = minimum number of edge colors
https://en.wikipedia.org/wiki/Vizing%27s_theorem every graph can be edge colored with close to the maximum degree (edge count on single vertex)

### Covering
<https://en.wikipedia.org/wiki/Covering_problems>


### Isomorphism
nauty
bliss
saucy

graph canonicalization. Find a way to sort vertices? If they all had unique attributes, sweet.
Then number of neighbors, other little facts. properties of neigbors
Could use properties of nehigbors
Could use labelling of neighbors too. That becomes a self consistent search. However, if you already know certain orderings (based on properties). Or you could branch
I'm not sure I'm understanding this the same way nauty does.


Graph hashing
https://github.com/calebh/dihash


disjoint set partition data structure?


isomorphism vs bisimulation. Different but related ideas.

automorphism - permutation of graph such that is an isomorphism
vertex orbit


[Practical graph isomorphism II](https://www.sciencedirect.com/science/article/pii/S0747717113001193)

Colorings are partitions. A mapping from vertices to numbers.
Refinement


```python
import pynauty

g = pynauty.Graph(10)
print(g)

```
Interning alpha equiv terms
graphlog. graphs as datalog objects. Graphs as the fundamental store.
automorphisms + group union find

AC terms are unstructure graphs
Typically terms are structured graphs.
```python
(1,(2,3))

def graph_from_term(t):
    tid = fresh()
    graph.add_vertex(tid)
    if isinstance(t,set):
        # for set or multiset we don't want the indirection

    for n,c in enumerate(t):
        graph.add_vertex(n) # add intermiedate node lbaelling which child. Or if we can edge label do that
        graph.add_edge(tid,n)
        cid = graph_from_vertex(c)
        graph.add_vertex(n,cid)
    return tid

```

```python
import networkx as nx
import matplotlib.pyplot as plt
def fun(name):
    def res(*args):
        G = nx.Graph()
        G.add_node(0)
        for arg in args:
            G = nx.disjoint_union(G,arg)
            G.add_edge(0,len(G) - len(arg))
        return G
    return res

def const(a):
    G = nx.Graph()
    G.add_node((0,a))
    return G
a = const("a")

plus = fun("+")
paa = plus(a,a)
G = plus(paa,paa)


nx.draw(G, with_labels=True)
#plt.show()


table = {}
def intern(G):
    h = nx.weisfeiler_lehman_graph_hash(G) # we should obviously cache this, but whatever
    matches = table.get(h) 
    if matches == None:
        table[h] = [G]
        return G
    else:
        if G in matches:
            print("found")
            return G
        for m in matches:
            #if m is G: # fast shortcutting
            #    return m
            #else:
            if nx.is_isomorphic(m,G):
                    print("iso")
                    return m
        matches.append(G)
        return G

a0 = intern(a)
print(table)
a = const("a")
a1 = intern(a)
print(table)
print(a1 is a0)

```


```python

table = {} # enumerating in toplogica order would be nice. OrderedDict. We seem to be fine though. default dict guarantees this?
class Node():
    def __init__(self,id, term):
        self.id = id # use id(Node) ?
        self.term = term
    def __hash__(self):
        return hash(self.id)
    def __eq__(self,b):
        return self is b #self.id == b.id ?
    def __repr__(self):
        return repr(self.term)
def hashcons(x):
    # x is hashable and equality.
    s = table.get(x)
    if s != None:
        return s
    else:
        n = Node(len(table), x)
        table[x] = n
        return n

def hashset(iter):
    s = frozenset(iter)
    return hashcons(s)

def reify(): # reify returns the set of all things we've seen so far. Well-founded. We could have tracked them.
    return hashset(table.values())
# reify is transitively closed

empty = hashset([])
one = reify()
two = reify()
three = reify()
print(three)
three2 = hashset([two, one, empty])
print(three2 is three)
print(three2.id)
print(three.id)
print(three2)
print(three)


def pair(a,b):
    return hashset([hashset([a]), hashset([a,b])])

print(pair("a","b"))
print(pair("a","b") is pair("a","b"))

def union(a,b):
    return hashset(a.term | b.term)

def trans(s):
    if isinstance(s.term, set):
        set(trans(x) for x in s.term)
        return 
    else:
        return s



```
Hmm. this is also basically a method for tree isomorphism. More or less follows the lins of the ahu algorithm.

Hash consing generates ids that witness the well foundedness.
hashunconsing

A unique id, but then we also kind of want to go back from id to terms. We could maintaini an id table, but from whence do we receive id?

Our memoizing table choices
- `Int -> Term`
- 

Hash consing does maximal compression to unique CSE form. To hash cons already built stuff _is_ to perform congruence closure? disjoint sets of tid.

```clingo

add(1,2,3).
add(1,2,4).
add(3,4,5).

root(Z,Z1) :- add(X,Y,Z), add(X1,Y1,Z1), root(X1,Xr), root(X,Xr), root(Y,Y2), root(Y1, Yr).


```

Hash consing is not appropriate for context dependency. The sharing is not dignified.
Bisimulation as equivalence
algebraic equivalence
graph equivalence

AC shuffling. Terms equal modulo AC. Terms equal modulo AC and Alpha. That's kind of cool.

query automorphisms - permutation symmettries of a conjunctive query.

query containment / query equivalence
```python
from z3 import *
S = Sort("S")
x, y, z = Consts("x y z", S)
R = Function("R", S,S,BoolSort())
Q1 = And(R(x,y), R()  )
Implies()
```



```clingo
h(X,Y)

```
Uniqueness is kind of easier to enforce than maximal sharing (?) because subgraph identity is tough. One incoming edge.
Forbid subgraph automorphisms? Can that be done?
A minimal (labeled/colored) graph that you have a homomorphism to. Does this minimal graph have automorphisms?


Approximate matching. Convex relaxation
Quadratic assignement problem
[On convex relaxation of graph isomorphism](https://www.pnas.org/doi/10.1073/pnas.1401651112)
MILP
A permutation matrix = 0-1 matrix with all  
$PBP^T = A$
doubly stochastic matrix


https://en.wikipedia.org/wiki/Graph_homomorphism generalization of coloring. colorings are homomoprhisms to complete graph

### subgraph isomorphgism
https://en.wikipedia.org/wiki/Subgraph_isomorphism_problem
subgraph matching and query containment



### Pfaffian orientation
https://en.wikipedia.org/wiki/Pfaffian_orientation
A directon to each edge such that each cycle
https://tex.stackexchange.com/questions/692892/kasteleyn-orientation-for-square-lattice

Kastelyn orietnation

[FKT algorithm](https://en.wikipedia.org/wiki/FKT_algorithm) for counting perfect matchings. Katelyn Temperley Fisher. Dimers.
pfaffian of skew symmettric matrix can be reduced to determinant
counting is useful in stat phys. entropy.
https://en.wikipedia.org/wiki/Geometrical_frustration
https://en.wikipedia.org/wiki/Holographic_algorithm


### Matchings
https://en.wikipedia.org/wiki/Matching_(graph_theory)
a set of edges such that none share vertices

maximum matching


https://en.wikipedia.org/wiki/Perfect_matching
pick edges such that exactly one edge touches every vertex

Related to https://en.wikipedia.org/wiki/Edge_cover where each vertex must touch at least one edge

## Graph rewriting
See term rewriting

double pushout.
A pattern L.
the "kept" bits K
the right hand side R, glued in

My temptation would be to: find a pattern L (using datalog/sql probably), store result in an env dict, blow it all away, paste in R filling in from the env.

The "env" can be represented as a graph homomorphism though from the pattern (a dictionary mapping vertices to vertices and edges to edges).

CHR

CHYP replacement

```prolog

morph(id,X,Y), morph(F,Y,Z) ==> morph(F,X,Z).
morph(swap, ...) %hmm.


graphize(id, X,Y) :- morph(id,X,Y).
graphize(comp(F,G), X, Z) :- %gensym(Y), 
                      graphize(F,X,Y), graphize(G,Y,Z).
graphize(otimes(F,G), [X,Y], [Z,W]) :- graphize()


graphize(id,X,X).
graphize(comp(F,G), X,Z) :- graphize(F,X,Y), graphize(G,Y,Z).
graphize(otimes(F,G), X-Y, Z-W) :- graphize(F,X-A, Z-B), graphize(G, A-Y,B-W). % difference lists. or append(X1,X2,X), 
graphize(swap, [A,B|Z]-Z, [B,A|Z]-Z).

% inverse collection out of chr
morph(F,A,B) \ collect(F,A,B)  ==> true.
collect(F,A,B), collect(G,B,C) ==> collect(comp(F,G),A,C).


auto :- autochr, deauto.

autochr

prove :- auto, rw(foo), simp, .


main() :- theorem(forall(X,foo(X)),
          (auto, simp, rw, )            
) 
vs
theorem(forall(X,foo(X))),
auto, simp, qed,

theorem(myname, forall(X,foo(X))).
auto. simp. qed.

% axiom
asserta(theorem(forall(X,foo(X)))).

axiom(F) :- asserta(theorem(forall)X,foo(X)).



```

## Misc
https://en.wikipedia.org/wiki/Graph_polynomial
Tutte polynomial


bipartite graphs

# Knots
https://en.wikipedia.org/wiki/Knot_polynomial


Rational Tangles - infinite series

# Matroids
See also abstract algebra

https://en.wikipedia.org/wiki/Matroid

"where greedy works"

https://en.wikipedia.org/wiki/Submodular_set_function


greedoids


# Packings

Circle packing. Really cool. A discrete analog of complex functions


# Combinatorics

Binomial

[Generating function](https://en.wikipedia.org/wiki/Generating_function)
[generatingfunctionology](https://www2.math.upenn.edu/~wilf/DownldGF.html)
[combinatorial species](https://en.wikipedia.org/wiki/Combinatorial_species)

https://doc.sagemath.org/html/en/reference/combinat/sage/combinat/species/species.html
https://hackage.haskell.org/package/species

Shadow calculus
Sums
https://en.wikipedia.org/wiki/Umbral_calculus

Concrete mathematics

PIE [principle inlcusion exclusion](https://en.wikipedia.org/wiki/Inclusion%E2%80%93exclusion_principle)

[pigeon hole principle](https://en.wikipedia.org/wiki/Pigeonhole_principle)
The continuous analog.

[polya enumeration theorem](https://en.wikipedia.org/wiki/P%C3%B3lya_enumeration_theorem) polya's theory of counting


handbook of combinatorics

https://en.wikipedia.org/wiki/Combinatorial_design 

Finite geometry

https://en.wikipedia.org/wiki/Incidence_structure 
# Ramsey Theory
Big step up in sophistication huh
Principles that 

Cody says has something to do with well quasi-orders


https://en.wikipedia.org/wiki/Schur%27s_theorem
https://mathworld.wolfram.com/SchurNumber.html
Schur number 5 = 161. 2017


[Ramsey number](https://mathworld.wolfram.com/RamseyNumber.html) solution to party problem. R(m,n) m know each other or n don't know each other.
Diagonal vs nondiagonal
2023 breakthrough on upper bound


# Logic
See lik the whole pile on logic

# Set theory
Ditto


# Order Theory
https://en.wikipedia.org/wiki/Order_theory

https://en.wikipedia.org/wiki/Dilworth%27s_theorem
Finite po-sets


https://en.wikipedia.org/wiki/Hasse_diagram visualizing posets


## Lattice
See also abstract algebra
