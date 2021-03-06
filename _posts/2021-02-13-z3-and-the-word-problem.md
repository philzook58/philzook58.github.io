---
author: Philip Zucker
date: 2021-02-13 
layout: post
title: Z3, The Word Problem, and Path Homotopy as Equality
categories:
- Formal Methods
tags:
- python
- category theory
- smt
- z3
---

There's a neat little trick I realized for encoding certain kinds of problems related to rewriting strings into Z3 somewhat elegantly. It's very simple too. 

### The Word Problem

The [word problem](https://en.wikipedia.org/wiki/Word_problem_(mathematics)) is figuring out if two strings can be made equal to each other with a pile of equations of substrings.
It can be thought of in different ways and shows up in different domains. One way to talking about it is as figuring out equivalaence for a finite presentation of a monoid. A finite presentation gives generators a,b,c let's say. The free monoid of these generators is just the strings you can make out these characters. The identity is the empty string and the monoid product is string concatenation. In a finite presentation, you also specify some equations like $ab=c$. Now it isn't obvious when two strings are equal or not.

There is however an obvious strategy to find equality. Just search. You can consider each string a node in a graph and each application of an equality somewhere in the string to be an edge on that graph. Keep trying equalities using Dijsktra's algorithm, A* or what have you and then if you find a path connecting the two words, you proved equality.

A more satisfactory solution is to use a completion algorithm like [Knuth Bendix](https://en.wikipedia.org/wiki/Knuth%E2%80%93Bendix_completion_algorithm). If Knuth bendix succeeds (a big if), the problem is in some sense solved for all words on the system. The output of the algorithm is a set of rewrite rules that bring words to a canonical form. You can just canonize words and compare to determine equality or disequality.

There are different approaches one might be inclined to take when modelling monoids in Z3. Z3 has a built in theory of strings, perhaps one could use arrays somehow, or one might axiomatize the theory directly using an uninterpeted sort like so.

```python
from z3 import *
G = DeclareSort("G")
e,a,b,c = Consts("e a b c", G)
times = Function('*', G,G, G)

monoid_axioms = [
  ForAll([a], times(e,a) == a ),
  ForAll([a], times(a,e) == a ),
  ForAll([a,b,c] , times(a,times(b,c)) == times(times(a,b),c))
]

```

Axiomatizing the sort literally transcribes the axioms of a monoid. The thing that isn't great about this is that the associativity law of the monoid is a derivation and you're going to waste Z3's energy on reasoning about trivial facts of associativity. It is preferable to have Z3 reason about something that is associative on the nose.

Well, there is a neat trick. The big thing that is associative on the nose is function composition. Instead of representing monoid elements as objects $a : G$, we represent them by a partial application of the monoid product $\hat{a} : G \rightarrow G = a\cdot -$ . We can always turn this representation back by applying it to the identity of the monoid $e : G$. This representation is associative on the nose for Z3.

We can make the presentation a little cuter to use by making a class that overloads multiplication and equality. Here we show a monoid generated by an element $a$ and with a quotienting equation $a^5 = a^2$.


```python
class Fun():
    def __init__(self, f):
        self.f = f
    def __mul__(self,g):
        return Fun(lambda x : self.f(g(x)))
    def __eq__(self,g):
        G = DeclareSort("G")
        x = Const("x", G)
        return ForAll([x], self.f(x) == g(x))
    def __call__(self,x):
        return self.f(x)
    def __pow__(self,n):
        if n == 0:
            return Fun(lambda x : x)
        return self * (self ** (n-1))

G = DeclareSort("G")
a = Fun(Function("a", G, G))

axioms = [a ** 5 == a**2] 

s = Solver()
s.add(axioms)
s.add( Not( a**6 == a**3)  ) # prove a**6 == a**3
s.check()
```

Viewed through a certain light it is another manifestation of the ole Hughes List/Cayley representation/Yoneda lemma thing, the gift that keeps on giving. The basic idea is to partially apply append/multiply/compose. It turns out the be useful to do in pragmatic programming context so because then things are associated in one direction by default instead of dealing with all possible associations. Some associations are better than others computationally, or it's nice to just have a canonical form as in this case. As it manifests in Z3, we represent monoid elements as single argument uninterpreted functions rather than as constants.

This representation also shows up in explaining how string rewriting can be easily emulated by term rewriting. The standard recipe says to convert each symbol of the string system into a single argument term. $a \implies a(X)$. Then convert the string rewrite rule abc -> bc becomes the term rewriting rule $a(b(c(X))) \rightarrow b(c(X))$, which is the same as the above.

### Finitely Presented Categories

This trick extends to categories. We can represent morphism equality checking of finitely presented categories in this style. The only change to the monoid case is that it seems conceptually cleaner that we want to make different Z3 sorts for the morphisms to go between, representing the objects of the category.
This transformation is probably a manifestation of the Yoneda Embedding, by analogy to the other examples that I do somewhat understand.
Here is a simple category with 2 objects, and generated by 2 morphisms $f : A \rightarrow B$ and $g : B \rightarrow A $ with the equation $f \cdot g \cdot f \cdot g = id$

```julia
# Hey Julia this time. Why not.
using PyCall
z3 = pyimport("z3")

ob = [z3.DeclareSort("Hom(-,A)") , z3.DeclareSort("Hom(-,B)")]
f = z3.Function("f", ob[1], ob[2])
g = z3.Function("g", ob[2], ob[1])
x = z3.Const("x", ob[2])
axiom = z3.ForAll([x], f(g(f(g(x)))) == x) # an equality over the morphism generators

s = z3.Solver()
s.add(axiom)
s.add(z3.Not( g(f(g(f(g(x))))) == g(x) )) # example simple theorem
s.check()
```


### Groups
The trick can also extend to groups, although dealing with the inverse operation of the group ruins the cleanliness. For every group element we add, we also need to add its inverse and some axioms about its inverse. So it isn't quite as clean as a monoid.

```python
class Fun():
    def __init__(self, f, inv):
        self.f = f
        self.inv = inv
    def __mul__(self,g):
        return Fun(lambda x : self.f(g(x)), lambda x : g.inv(self.inv(x)) )
    def __eq__(self,g):
        G = DeclareSort("G")
        x = Const("x", G)
        return And(ForAll([x], self.f(x) == g.f(x)), ForAll([x], self.inv(x) == g.inv(x)))

    def inv(self):
        return Fun( self.inv, self.f )
    def __call__(self,x):
        return self.f(x)
    def __pow__(self,n):
        if n == 0:
            return self.id
        return self * (self ** (n-1))
    def inv_axioms(self):
        G = DeclareSort("G")
        x = Const("x", G)
        return And(ForAll([x], self.f(self.inv(x)) == x), ForAll([x], self.inv(self.f(x)) == x) )
    
Fun.id = Fun(lambda x: x, lambda x: x)
def GroupElem(name):
    return Fun(Function(name,G,G), Function(f"inv_{name}",G,G))


# Symmetric group
N = 3
sigma = [GroupElem(i) for i in range(N)]

axioms = [s.inv_axioms() for s in sigma]
axioms += [ sigma[i]*sigma[i] == Fun.id for i in range(N) ]
axioms += [ sigma[i]*sigma[j] == sigma[j] * sigma[i] for i in range(N) for j in range(i-1)]
axioms += [ sigma[i]*sigma[i+1]*sigma[i] == sigma[i+1] * sigma[i] * sigma[i+1] for i in range(N-1)  ]


# A braid group
# A nice way to detangle knots with egg?
N = 3
sigma = [GroupElem(f"sigma_{i}")for i in range(N)]

axioms = [s.inv_axioms() for s in sigma]
axioms += [ sigma[i]*sigma[j] == sigma[j] * sigma[i] for i in range(N) for j in range(i-1)]
axioms += [ sigma[i]*sigma[i+1]*sigma[i] == sigma[i+1] * sigma[i] * sigma[i+1] for i in range(N-1)  ]
```


### Path Connectivity


Here is another example where an encoding allows us to greatly change the ease with which Z3 handles a problem. This example feels a little different from the others, or is it?


Naively one might try to encode path connectivity of two vertices using a predicate `connected`

```python
Point = DeclareSort("Point")
connected = Function("connected", Point, Point, Bool)
#This defines a predicate that says if a point is connected to another.

axioms = []
#paths are invertible
axioms += ForAll([x,y], path(a,b) == connected(b,a))

# transitivity
axioms += ForAll([x,y,z], Implies( And(connected(x,y) , connected(y,z) ) , connected(x,z) ))

# self paths.
axioms += ForAll([x], connected(x,x))
```

Built in equality already _has_ these properties though. Equality is backed by more or less a disjoint set data structure which is a very efficient way to calculate the connected sets of a graph. 

I can guarantee you that this formulation will work better.

```python
import networkx as nx

G = nx.Graph()
G.add_nodes(['a','b','c','d'])
G.add_edges( [('a','b'), ('b','c'), ('c','d') ] )
G.connected_components
```

```python
Vertex = DeclareSort("Vertex")
a,b,c,d = Consts("a b c d", Vertex)

edges = [a == b, b == c, c == d]

s = Solver()
s.add(edges)
s.add(a != d)
s.check() # unsat means a and d are connected 
```

### Path Homotopy

The paths through the triangulation of a surface form a category with vertices as objects and paths as morphisms. [Homotopically](https://en.wikipedia.org/wiki/Homotopy) equivalent paths also form a category, a [groupoid](https://en.wikipedia.org/wiki/Groupoid) even.

This is to the group example what the Category example was to the monoid.

There is something very tickling about using Z3 equality to express homotopy equivalence. It is very vaguely reminiscent of things that occur Homotopy Type Theory, but I wouldn't take that too seriously.


### Bits and Bobbles

The underlying data structure here is the Egraph. Specializing EGraphs to single arguments terms might give something interesting. Also then we open up the ability to mix in Tries.

How do you prove two things are _not_ equal? Find a model?

How to deal with higher homotopies? Does the existence of cubical type theory suggest in some sense that a data structure for binding forms (de bruijn perhaps ) is a useful but unexpected one for describing concrete homotopies on concrete triangulations.

Using egg <https://egraphs-good.github.io/> for braid groups. Braid groups have applications in topological quantum computation. Optimizer?


2-homotopies - horizontal and vertical composition.

Talia Ringer and cubical type theory <https://twitter.com/SandMouth/status/1330027900804935684?s=20>

Gershom Bazerman and topology of rewrite systems <https://paperswelove.org/2017/video/gershom-bazerman-homological-computations/>

Edit: Michael Misamore on twitter brings up an interesting application I was not aware of. Apparently the concept of homotopy is useful in concurrency theory. <https://twitter.com/m_misamore/status/1360957349658316802?s=20>
<http://www.jeremy-gunawardena.com/papers/hac.pdf>
<http://www.lix.polytechnique.fr/Labo/Samuel.Mimram/hcr.html>
<http://boole.stanford.edu/pub/hda.pdf>

I don't know if Z3 is useful here or not.





String rewriting is the analog of find/replace in your text editor. It finds an exact match and will replace it.
You can emulate a string rewriting system by putting the starting string into you text editor and iteratively applyying replace all

Or you can run the following sed script.

Term rewriting where the patterns are ground terms can be easily emulated by string rewriting. You can take any tree structure and flatten/serialize it via a traversal.

So the difference is not so much terms vs strings as it is some kind of flexibility in the patterns. In some more global sense, they are both turing complete (right?) and are equivalent anyway, and yet I think it's impossible to shake the sense that term rewriting is the more powerful system.

Term and String systems are interrelated in interesting ways. Many term indexing structures are built by taking some kind of string indexing structure like a trie on flattened terms.

Function composition is an associative operation "on the nose" in a way that many other definitions are not. By embedding your concept in terms of it, you get associativity for free.

There's something here that is prevalent in mathemtics.
Hughes lists convert list to a functional form because different associations of list appending have different performance characteristics. By Preapplying append in the right way, you guarantee by construction and by the natural of function composition.
The Cayley representation of a group is an example of a similar thing.
The Yoneda representation of a category.
