



It is a wise goal in programming and logic is to try to express your problem as naturally as possible in the system you're working in. You can hack unnatrual abstractions into systems, but you're probably gonna have a bad time. Functional programming in C, dependent types in Rust, etc.

The Z3 input language is highly expressive, being some variant of first order multi -orted logic. It is more expressive than Z3 solver can always handle (although I've been pleasantly and unpleasantly surprised. YMMV), especially when you start using lots of quantifiers.
One can express sophisticated concepts in first order logic. Standard set theory is more or less expressed in first order logic (with some nasty axiom schema). But these encodings are somewhat gnarly and unnatural and they hide all the semantic domain specific information that you use to reason about them so effectively.
Z3 does have a really good understanding of certain topics though. It understand linear inqualities, bitvectors, bools, algerbaic datatypes, a notion of equality, and a notion of an uninterpeted function (congruence closure `a == b => f(a) == f(b)`). If you can find a way to encode to that stuff in a not totally horrible way and work with Z3, it seems more likely things will go well.

Consider the following

```python
Point = DeclareSort("Point")
path = Function("path", Point, Point, Bool)
#This defines a predicate that says if a point is connected to another.

axioms = []
#paths are invertible
axioms += ForAll([x,y], path(a,b) == path(b,a))

# transitivity
axioms += ForAll([x,y,z], Implies( And(path(x,y) , path(y,z) ) , path(x,z) ))

# self paths.
axioms += ForAll([x], path(x,x))
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

It's a little hacky and odd though. Why are we considering equality to be a notion of connected? How weird.

But Homotopy type theory makes a precedent of using equality as some notion of path.



### Encoding Paths of Paths into Z3

The `path` predicate formula didn't seem so bad for connectivity. But suppose we want to reason about homotopies. Homotopies are deformations of two paths with shared endpoints into one another.

We can make a discretized analog of the conitnuous concept by considering triangulated surfaces. Each triangle face describes a primitive homotopy move of pushing a path across that face. Alternatively we can discretize into grids, and then each box is a primitive homotopy move.

### String Rewrite Systems

String rewriting is the analog of find/replace in your text editor. It finds an exact match and will replace it.
You can emulate a string rewriting system by putting the starting string into you text editor and iteratively applyying replace all

String rewriting can be easily emulated by term rewriting. Convert each symbol of the string system into a single arguyment term. a -> a(x). Then the string rewrite rule abc -> bc becomes the term rewriting rule $a(b(c(X))) -> b(c(X))$

Or you can run the following sed script.


Term rewriting where the patterns are ground terms can be easily emulated by string rewriting. You can take any tree structure and flatten/serialize it via a traversal.

So the difference is not so much terms vs strings as it is some kind of flexibility in the patterns. In some more global sense, they are both turing complete (right?) and are equivalent anyway, and yet I think it's impossible to shake the sense that term rewriting is the more powerful system.

Term and String systems are interrelated in interesting ways. Many term indexing structures are built by taking some kind of string indexing structure like a trie on flattened terms.





### Bits and Bobbles

Function composition is an associative operation "on the nose" in a way that many other definitions are not. By embedding your concept in terms of it, you get associativity for free.

There's something here that is prevalent in mathemtics.
Hughes lists convert list to a functional form because different associations of list appending have different performance characteristics. By Preapplying append in the right way, you guarantee by construction and by the natural of function composition.
The Cayley representation of a group is an example of a similar thing.
The Yoneda representation of a category.

2-homotopies - horizontal and vertical composition.

Talia Ringer and cubical type theory

Gershom Bazerman and topology of rewrite systems

Does cubical type theory suggest in some sense that a data structure for binding forms (de bruijn perhaps ) is a useful but unexpected one for describing concrete homotopties