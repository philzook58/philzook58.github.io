```python
from dataclasses import dataclass, field

@dataclass
class UF():
    uf : list[int] = field(default_factory=list)
    def makeset(self):
        eid = len(self.uf)
        self.uf.append(eid)
        return eid
    def find(self, x):
        while self.uf[x] != x:
            x = self.uf[x]
        return x
    def union(self, x, y):
        x,y = self.find(x), self.find(y)
        if x != y:
            self.uf[x] = y
        return y
    def rebuild(self):
        for i in range(len(self.uf)):
            self.uf[i] = self.find(i)

uf = UF()
for i in range(10):
    uf.makeset()
uf.union(0, 1)
uf.union(1, 2)
uf.rebuild()
uf
```




    UF(uf=[2, 2, 2, 3, 4, 5, 6, 7, 8, 9])



A persistent union find retains all old versions of the union find

a colored / linked / refiniing / hiearchical union find has multiple refining union finds hanging around. Unions higher in the herarchy are inherited by ufs lower in the hierarchy. 

A contextual union find is like this with the added feature that the ufs are identified with contexts. When contexts become equivalent, the appropriate unuion finds should become equivalent. When a context is subsumed,it should inherit the equality infromation of the subsumee. 

Subsumption is a better mechanism than lattices for contexts. While there is a lattice, it's a weird one. Subsumption is more of a direct translation


Equating two nodes in a colored union find makes a new node? Multiparent. Maybe you have to ping pong until convergence. I think the contracting nature of the maps means this'll work. You only have to ping pong up to common ancestor.
Equating two color nodes goes into a meta-union find or color nodes? You need to ping pong through the entire tree, or normalize everything in the root node.
a meta meta union find?
Really you can assert node1 <= node2.

class DiffUF():
    ufs: list[UF]
    self.duf

class DiffUF():
    parent | self.uf, self.duf  # either points to equivalent parent UF or actually has the data and pointer to inehritance uf.



```python
class DiffUF():
    def __init__(self, uf : UF):
        self.uf = uf
        self.duf = {}
    def makeset(self):
        return self.uf.makeset()
    def find(self, x):
        x = self.uf.find(x)
        while x in self.duf:
            x = self.duf[x]
        return x
    def union(self, x, y):
        x,y = self.find(x), self.find(y)
        if x != y:
            self.duf[x] = y
        return y
    def __hash__(self):
        return hash(tuple(sorted(self.duf.items())))
    def __le__(self, other):
        if len(self.duf) > len(other.duf): # fast check
            return False
        return all(other.find(k) == other.find(v) for k,v in self.duf.items())
    def __eq__(self, other):
        return len(self.duf) == len(other.duf) and self <= other # ? Right?
    def __or__(self, other): # over same base
        """
        Union find join. Finest partition greater than both.
        """
        assert id(self.uf) == id(other.uf)
        new = DiffUF(self.uf)
        new.duf = self.duf.copy() # or pick biggest one
        for k,v in other.duf.items():
            new.union(k,v)
        return new
    def __and__(self, other): # over same base
        """union find meet. Coarsest partition less than both."""
        assert id(self.uf) == id(other.uf)
        new = DiffUF(self.uf)
        for k,v in self.duf.items():
            if other.find(k) == other.find(v):
                new.union(k,v)
        return new
    def rebuild(self): # canon
        old_duf = {}
        self.duf = {}
        self.uf.rebuild()
        for k,v in old_duf.items():
            self.union(k,v)
    
    
```

https://usr.lmf.cnrs.fr/~jcf/publis/puf-wml07.pdf  A Persistent Union-Find Data Structure

Proof producing 

1. Tie braking
2. Path compress or no
3. edge storage, attributed storage
4. Pointers, array, or dict
5. Lazy vs eager

A purely function union find using purely functional distionaries


Union finds solve connectivity in graphs. Proof producing UF stores a spanning tree also so that it can return a path when you ask for it.


Layered union finds are like layered theories
`M1 |= M2 |= M3 |= M4 ...`


A canonizer uf would want to update all the children to be updated too.






```python
@dataclass
class EagerUF():
    uf : list[int] = field(default_factory=list)
    def makeset(self):
        eid = len(self.uf)
        self.uf.append(eid)
        return eid
    def find(self, x):
        return self.uf[x]
    def union(self, x, y):
        x,y = self.find(x), self.find(y)
        if x != y:
            self.uf[x] = y
            self.rebuild()
        return y
    def rebuild(self):
        for i in range(len(self.uf)):
            self.uf[i] = self.find(i)
```


```python
class FrozenDict()
```

You don't _have_ to structurally canonicalize to implement a correct hash.
But you kind of might as well



```python
@dataclass(frozen=True)
class CanonUF():
    uf : tuple[int,...]
    @classmethod
    def create(cls):
        return CanonUF(())
    def makeset(self):
        eid = len(self.uf)
        self.uf.append(eid)
        return CanonUF(self.uf + (eid,))
    def find(self, x):
        return self.uf[x]
    def union(self, x, y):
        x,y = self.find(x), self.find(y)
        if x != y:
            self.uf[x] = y
            self.rebuild() # rebuild immeidately
        return y
    def __hash__(self):
        return hash(self.uf)
    def __eq__(self, other):
    def rebuild(self):
        for i in range(len(self.uf)):
            self.uf[i] = self.find(i)
```


```python
class ContextUF():
    base : UF
    ctxs : dict[CanonUF, DiffUF] #  ctx |- res 
    def __init__(self):
        self.base = UF()
        self.ctxs = {}
    def rebuild(self):
        newctx = {}
        for ctx, uf in self.ctxs.items():
            ctx1 = ctx.rebuild()
            for ctx1, uf1 in self.ctxs.items():
                if ctx <= ctx1:
                    uf1.merge(uf)
            newctx[ctx.rebuild()] = uf.rebuild()
        self.base.rebuild()



```

# Persistent
https://github.com/MagicStack/immutables
https://github.com/tobgu/pyrsistent
https://discuss.python.org/t/pep-603-adding-a-frozenmap-type-to-collections/2318/219



```python
! python3 -m pip install immutables
```

    Collecting immutables
      Downloading immutables-0.21-cp312-cp312-manylinux_2_5_x86_64.manylinux1_x86_64.manylinux_2_17_x86_64.manylinux2014_x86_64.whl.metadata (4.5 kB)
    Downloading immutables-0.21-cp312-cp312-manylinux_2_5_x86_64.manylinux1_x86_64.manylinux_2_17_x86_64.manylinux2014_x86_64.whl (104 kB)
    Installing collected packages: immutables
    Successfully installed immutables-0.21



```python

```

# Bits and Bobbles

I called it base. Are fibers leaking into my thinking?
 
I have meet and join of uf. A heyting algerba if I can define an A => B? Probably the finest partition that when merged with A gives B or is less than B? C /\ A  <= B

def diff(self, other):

![](https://en.wikipedia.org/wiki/File:Set_partitions_4;_Hasse;_circles.svg) partition refinement https://en.wikipedia.org/wiki/Partition_of_a_set

## old 
```python

```

Simple union find

compressing

colored union finds - use min to ping pong. label the union find. DAG hierarchy is fine.

union finds as converging functions

proof pdoucting union find


using dictionary vs using ids
vs using pointers

The z3 egraph and doubly linked lists. If we want to retain _down_ pointers it is abboying because there mightb e multiple children to one parent. But you can insert yourself into a doubly linked list via the dasncing link technique.
Hmm. Maybe this is why z3 does it this way. For fast backtracking https://z3prover.github.io/papers/z3internals.html#sec-equality-and-uninterpreted-functions



```python
from dataclasses import dataclass
class UF():
    uf : list[int]
    def find(self, x):
        while x != self.uf[x]:
            x = self.uf[x]
        return self.uf[x]
    def makeset(self):
        self.uf.append(len(self.uf))
        return len(self.uf) - 1
    def union(self, x, y):
        self.uf[self.find(x)] = self.find(y)
        return self.find(y)

uf = UF()
a, b, c = uf.makeset()


```


    ---------------------------------------------------------------------------

    AttributeError                            Traceback (most recent call last)

    Cell In[1], line 16
         13         return self.find(y)
         15 uf = UF()
    ---> 16 uf.ma


    AttributeError: 'UF' object has no attribute 'ma'



```python
from dataclasses import dataclass
@dataclass
class Cell():
    name: str
    id: int
    parent: 'Cell'
    def __init__(self, name="_"):
        self.parent = self
        self.id = id(self)
        self.name = name
    def find(self):
        x = self
        while x.parent is not x:
            x = x.parent
        return x
    def union(self,y):
        self.find().parent = y.find()
        return y.find()
    
x = Cell("x")
y = Cell("y")
z = Cell("z")
print(x.parent)
x.union(y)
y.union(z)
print(x.find() == z.find())
print(x)
print(z)
```

    Cell(name='x', id=136449433498864, parent=...)
    True
    Cell(name='x', id=136449433498864, parent=Cell(name='y', id=136449433498432, parent=Cell(name='z', id=136449433492432, parent=...)))
    Cell(name='z', id=136449433492432, parent=...)



```python
reasons = []
trace = []
def union_reason(x, y, reason):
    reasons[find(x)] = (x, y, reason)
    trace.append((x, y, reason)) # this is sufficient. we don't need to store find(x) and find(y)
    uf[find(x)] = find(y)
    return find(y)

def explain(x,y):
    
```

Visualizing as a graph.
The union find is part of kruskal's algorithm
https://en.wikipedia.org/wiki/Kruskal%27s_algorithm

So for example if you had a bunch of equalities and you know how painful each one was to get, you could devise a minimum spanning tree for that.

Term rewriting as a graph.

Secret congruence edges



```python
import networkx as nx

# random graph with multiple components
G = nx.Graph()
#G.add_nodes_from(range(10))



# color the edges in the union find
```


```python
# vectorized normalization.
# For egraph purposes, not being fully normalized isn't really a problem.

import numpy as np

uf = np.arange(10)
uf[8] = 0
uf[0] = 4

def normstep(uf):
    return uf[uf] 

normstep(uf)

def step2(uf):
    return uf[uf[uf]]
step2(uf)

```




    array([4, 1, 2, 3, 4, 5, 6, 7, 4, 9])



