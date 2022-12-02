---
date: 2022-11-25
layout: post
title: "Groupoid Annotated Union Finds"
description: You can annotate union finds with groupoids instead of groups. Egraphs?
tags: logic egraphs
---

The union find is also known as the disjoint set datastructure. It supports the operations of union, which merges two sets, and find, which figures out which set an element is in. Sets are identified by picking a canonical element per set.

It works by building a forest of trees, one for each disjoint set. In these trees, the children have pointers to their parents, which makes it feel different than trees like ASTs that may be more familiar, which more commonly have pointers to their children.

The flatter the tree, the less indirection there is to lookup the canonical element (the root) in each set. Because of this, the tree is compressed upon find operations by changing the parent pointer to point to the parent of the parent.

When I first heard of this, I was confused. What do I need that for? Now it is one of my favorite data structures.

- Finding connected components in a graph
- Unification
  - type inference
  - prolog
  - automated theorem proving
- E-graphs
- Compilers


One might be tempted to build such a structure as just described by using pointers or references. This is possible, but more commonly one uses an array, with array indices acting as node pointers/identifiers. This is actually a rather interesting observation that data structures that one may think need pointers can be treated in this way generally. Pointers are a intrinsic meta level map that compting systems tend to offer. You can replace their usage in many (all?) cases with a Map from integers to items, aka an array. There are benefits of memory safety and cache friendliness to doing so. This is sometimes called using a memory arena.

From a more [mathematical perspective](https://en.wikipedia.org/wiki/Equivalence_relation), preimages of any function form disjoint sets, which can be considered equivalence classes. The union find is defining a contracting mapping $f$ from the items to themselves (the trees look like funnels). This map eventually reaches a fixed point whenever you iterate it $fix(f) = f(f(f(f(...))))$. The equivalence classes defined by te union find are the preimage of this fixed point. Path compression is generating a new, more quickly contracting map with the same fixed points.

Here's a basic bad union find with no path compression and no smart parent setting in union. See how easy that is?

```python
class BadUF():
  # no path compression. no depth stroage.
  def __init__(self):
    self.parent = []
  def find(self,i):
    p = self.parent[i]
    while p != self.parent[p]: 
      p = self.parent[p]
    return p
  def makeset(self):
    x = len(self.parent) # right? 
    self.parent.append(x)
    return x
  def union(self,i,j):
    i = self.find(i)
    j = self.find(j)
    self.parent[i] = j
    return j
```

The union find achieves linear space to store an equivalence relation. Naively storing an equivalence relation takes N^2 space, so this is impressive. Testing if two items are in the same eclass can be brought down to nearly constant time.

# Union Find Annotations

There is an interesting extension to the union find that I can't get out of my head. One can Annotate the edges of the union find.

I've discussed before that it is easy enough to annotate the vertices of the union find with the [union find dict](https://www.philipzucker.com/union-find-dict/).

The naive N^2 representation of a union find can support (multiple) annotations on the edges as a table `eq(x,y,annot)`. This may be seen as a form of contextual equality. This is N^2 annotations we somehow have to get down to linear space. The annotations need to have a certain structure to make sense in the union find representation.

Exactly what properties does this annotation need? It's a little confusing.

The union find is expressing that somehow in the children parent chain `a->b->c`, `a` is also transitively related to `c` via `b`. If we need to carry annotations through this transitivity `a -g1> b -g2> c`, we need to have a notion of composition or multiplication of annotations `a -(g1 . g2)> c`.

In the situations `a -> b <- c`, we also seem to want `a` and `c` to be related via their relationship to `b`. But now the arrows point the wrong way. So we need some notion of flipping the relation around. If we want this to be conservative, this flipping around needs to be some kind of inverse.

Finally `a` is by default related to itself. There is some kind of notion of a null relationship, or identity. It is sometimes the case that the root of a union find is denoted by a self reference. Or it can be noted by a special marker.

[Ed Kmett has given multiple talks about this idea](https://youtu.be/KxeHGcbh-4c?t=1254). In his presentation, the annotations are group elements which are interpreted as being a [group action](https://en.wikipedia.org/wiki/Group_action) upon the items of held in the union find. The orbits of elements under the group action will be the things related in the union find. 

Interesting groups include:
- Addition of real or integers
- Vector addition
- Multiplication of (nonzero) reals or integers or complex numbers
- (invertible) Matrix multiplication
- Rotations
- Translation
- Affine transformations
- Booleans under not.

He mentions unification modulo group action is tractable apparently, even though many extensions to unification aren't (_general_ [e-uniification](https://en.wikipedia.org/wiki/Unification_(computer_science)#E-unification) and _full_ higher order unification are quite hard. The trick seems to be finding the subcases of these problems that are tractable). It seems to be the case that you don't want significant search inside your unification algorithm for most applications. Keep it separate. You can have group annotations on every subterm like `(0+)f((8+)Y) = (0+)f((3+)X)` would have the solution `X = (5+)Y` using the addition group.

Yihong points out <http://poj.org/problem?id=2492> as a competitive programming exercise that can use this trick. 
 
The "generalized union find" is mentioned in chapter 10 of the [Constraint Handling Rule (CHR) book](http://www.informatik.uni-ulm.de/pm/fileadmin/pm/home/fruehwirth/constraint-handling-rules-book.html). This has a slightly different perspective on the annotations. They speak of them as representing a relation between the items. Relations have a notion of composition, "inverse" (converse), and identity similar to that of a group. Although relational converse is more like a matrix transpose than a matrix inverse, which is kind of interesting as it leaves open the possibility of nonconservative things happening in the annotations. The standpoint there is that there is a relation algebra closed under these operations. The collapsing of this algebra (forgetting these annotations by taking the union of all the relations at play) is an equivalence relation. This notion does generalize the idea of group action annotations I believe. Objects in group action orbits are G-related to one another, with relational comp, inverse, and identity corresponding to the group notions. 

I think an interesting 3rd standpoint is that a groupoids can also for the basis for an acceptable union find annotation. Groupoids can be characterized as partial groups or categories wth inverses. Interpreting the items in the union find as objects, this makes sense. The union find is then interpreted as representing the partial (dependent) function `forall a b : Ob, Hom(a,b)` rather than the partial function `X -> X -> G` like in the group annotation. Maybe since the groupoid has to play nice/coherently with union find edges, we should describe the annotation union find as describing a functor from the equivalence relation considered as a category to the groupoid, which each edge picking out a groupoid element in such a way as that all transitive multiplications work.  

This groupoid business is particularly intriguing on a couple fronts. The whole reason I've heard of groupoids is that they come up in models of the identity type in dependent type theory and in HoTT.

The second reason is that simple example of a groupoid is paths on an undirected graph. These correspond to proof objects in the [proof producing union find](https://www.cs.upc.edu/~roberto/papers/rta05.pdf). If one hash-conses these proof objects or allows an indirection, it isn't that bad to be storing "the entire path" as in the naive version below. The e-graph is already a natural hash-conser. By puncturing the barrier between these annotation and the egraph itself, we can gain a programmable notion of annotation. One downside might be that we are eagerly producing proofs rather than on demand?

The third reasons is that egglog is all about partiality and groupoids have partial composition.

In any case, the operational interface between all of these is the same. It just isn't quite clear exactly what laws compose, id, and inv should have.


```python
class UFGroupoid():
  # no path compression. no depth stroage.
  def __init__(self, id_, compose, inv):
    self.parent = []
    self.annot = []
    self.id = id_
    self.compose = compose
    self.inv = inv

  def find(self,i):
    p = self.parent[i]
    g = self.annot[i] # i -g> parent
    while p != self.parent[p]:
      g = self.compose(self.annot[p],g)
      p = self.parent[p]
    return p, g
  def makeset(self):
    x = len(self.parent) # right? 
    self.parent.append(x)
    self.annot.append(self.id)
    return x
  def union(self,i,j,g):
    i,gi = self.find(i)
    j,gj = self.find(j)
    if i == j:
        #if gj == self.compose
        #if len(g) <= len(gj) + len(gi):
        #    self.annot[i] 
        # naw. Least common ancestor. bleh.
        # There might be a way to mix in a notion of "best" groupoid element here.
        # by comparing g and gi * inv(gj)
        return i
    self.parent[i] = j
    self.annot[i] = self.compose(self.inv(gj), self.compose(g, self.inv(gi)))
    return j

def compress_append(xs,ys):
    # basically lambda x,y: x + y except we remove backtracking along exact same path
    # That makes inverse an actual inverse.
    res = [x for x in xs]
    for y in ys:
        (a,b) = y
        if len(res) > 0 and (b,a) == res[-1]:
            res.pop()
        else:
            res.append(y)
    return res
uf = UFGroupoid([], compress_append, lambda x: [(y,x) for (x,y) in reversed(x)])
a = uf.makeset()
b = uf.makeset()
c = uf.makeset()
d = uf.makeset()

uf.union(a,b, [(b,a)]) # 2,1
uf.union(b,c, [(c,b)]) 
uf.union(a,d, [(d,a)])
print(uf.find(a))
print(uf.find(b))
print(uf.find(c))
print(uf.parent)
print(uf.annot)
'''
(3, [(3, 0)])
(3, [(3, 0), (0, 1)])
(3, [(3, 0), (0, 1), (1, 2)])
[1, 2, 3, 3]
[[(1, 0)], [(2, 1)], [(3, 0), (0, 1), (1, 2)], []]
'''

# a group example
uf = UFGroupoid(0, lambda x,y: x + y, lambda x: -x) # lambda x,y: x + y
a = uf.makeset()
b = uf.makeset()
c = uf.makeset()
d = uf.makeset()

uf.union(a,b, 1) 
uf.union(b,c, 1) 
uf.union(a,d, 3)
print(uf.find(a))
print(uf.find(b))
print(uf.find(c))
print(uf.parent)
print(uf.annot)
'''
(3, 3)
(3, 2)
(3, 1)
[1, 2, 3, 3]
[1, 1, 1, 0]
'''
```


# Bits and Bobbles

There might also be utility in storing a (finite?) _set_ of groupoid elements `forall a b : Ob, Set (Hom a b)` also, but I'm not sure. The groupoid multiplication naturally lifts to set of groupoid multiplication. This set lifted version is non-conservative in a sense that the sets may grow under path compression.

Instead of insisting that the annotations are completely recoverable or invertible no matter the compression, we could insist that they are monotonic. There are certain advantages to ignoring compression entirely. Proof producing union finds sort of store both a compressed and uncompressed version

We might want the union find tree to pick edges with minimum cost. There may be a way to use Minimum spanning tree algorithms to pick "good" union find trees. In the datalog context where annotations can be implicilty produce by rules this might make sense. Regular union find is a subcase of MST with 0 cost weight. Then all spanning trees are  equivalent. This might be a method to acheve "best" (weakest) contexts on eq edges. It's not particularly apparent different schemes of doing this converge to a unique fixed point.

Starts to look like allegories.

We do probably want the annotations to mean the same thing regardless of the order of insertion or tie breaking method.

- Path Compression or no
- tie breaking methods for union.

A really convenient tie breaking method is to use max or min.

Can this be used for contextual equalities? I know of no notion of context that forms a group structure

Can this be used for equality modulo alpha equivalence (permutation group or isomorphisms) ? Nominal logic.



Egraph Functions that are group invariant can compress themselves by ignoring the group annotations.
Functions that behave interestingly under group annotations (like vector valued functions or $e^{ikx}$ under translation) can have custom congruence laws. These custom congruence rules feels similar to [Coq Setoid system](https://coq.inria.fr/refman/addendum/generalized-rewriting.html).