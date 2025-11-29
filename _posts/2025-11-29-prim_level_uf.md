---
title: Primitive, Leveled, and Quantifier Union Finds
date : 2025-11-29
---

There is an interesting and simple union find variation that allows primitives into the union find.

I think this could make for a nicer experience possibly in egg or egglog, where you don't need functions to transfer between primitives and uninterpreted sorts. SMT does not require such a distinction and it is a small inelegance IMO to require it. eclass-like entities should behave more like SMT constants (like `smt.Int("x")`) and primitive entities should be like SMT values (like `smt.IntVal(1)`). SMT allows these things to be equated.

There is also a concept called levels I've seen in Hindley Milner type checking which I think can be reified as a union find variation.

If you combine these two things, you get a union find that works for atomic equational problems under a quantifier prefix.

# Basic Union Find

A basic union find can be built in an arena style. We use integers as identifiers, wrapped in a tuple to distinguish them from primitive integers to come next.

`find` looks up in the parent table iteratively to find a root. I ignore path compression but it's nice to do.

`union` finds the roots and then sets one root equal to the other. There is a lot of flexibility in the ordering which can be used for various purposes (as we'll see some of).

A regular union find is a useful thing for finding minimal (least equations) /maximal (most elements) models for atomic equations `a = b /\ b = c /\ d = e` but also similarly find atomic equational proofs.

The `parents` relationship can be written in RefCell, Dictionary, or Arena style which are basically equivalent but can make the mind go in different directions. It is tougher to bundle up the entire union find in RefCell form.

```python
from dataclasses import dataclass, field
from typing import NamedTuple

class EId(NamedTuple):
    id : int

@dataclass
class UFArena():
    parents : list[EId] = field(default_factory=list)
    def makeset(self):
        eid = EId(len(self.parents))
        self.parents.append(eid)
        return eid
    def find(self, x : EId):
        while self.parents[x.id] != x:
            x = self.parents[x.id]
        return x
    def union(self, x, y):
        x,y = self.find(x), self.find(y)
        if x != y:
            if x < y:
                x,y = y,x
            self.parents[x.id] = y
        return y
```

Some usage

```python
uf = UFArena()
x,y,z,w = [uf.makeset() for i in range(4) ]

uf.union(x, y)
uf.union(y, z)
assert uf.find(z) == uf.find(x)
uf
```

    UFArena(parents=[EId(id=0), EId(id=0), EId(id=0), EId(id=3)])

# Primitive Union Finds

We can extend the previous union find by allowing more than just eids into the parents table.

Now we have to tie break when we union an eid to a primitive such that the primitive becomes the root. Primitives "win".

If we union two distinct primitives, we need some method to resolve them or throw an error. If we resolve tree-like primitives structurally, we get something similar to a syntactic unification routine.

In a more low level implementation, primitives may be required to either fit into a machine word or be held in a separate interning table.

Other names that I like are "Atoms" or "Rigids" rather than "primitive". Primitive implies that it is something like `i64` but there is utility to other examples that are abstract uninterpreted entities and yet still rigid, whereas eids are flexible.

```python
@dataclass
class PrimUF():
    parents : list[EId | object] = field(default_factory=list)
    def makeset(self) -> EId:
        eid = EId(len(self.parents))
        self.parents.append(eid)
        return eid
    def find(self, x : EId | object):
        while isinstance(x, EId) and self.parents[x.id] != x:
            x = self.parents[x.id]
        return x
    def resolve(self, x, y):
        # You can add in something that replicates unification without occurs check
        if isinstance(x, tuple) and isinstance(y, tuple) and len(x) == len(y):
            return tuple(self.union(a,b) for a,b in zip(x,y))
        else:
            raise Exception("Conflict", x, y)
    def union(self, x : EId | object, y : EId | object):
        x,y = self.find(x), self.find(y)
        if x == y:
            return y
        else:
            if not isinstance(x, EId):
                if isinstance(y, EId):
                    x,y = y,x
                else:
                    return self.resolve(x,y)
            self.parents[x.id] = y
            return y

```

```python
uf = PrimUF()
x,y,z,w = [uf.makeset() for i in range(4)]
uf.union(x, y)
uf.union("fred", y)
uf.find(x)

```

    'fred'

A little bit of unification. We do not implement an occurs check, which is overplayed anyway IMO.

```python
uf.union((w,1), (2,1))
uf.find(w)
```

    2

```python
uf
```

    PrimUF(parents=[EId(id=1), 'fred', EId(id=2), 2])

# Leveled Union Find

In classic Hindley Milner type inference, when you exit `let` nodes, you generalize the type variables introduced inside that `let`. You don't generalize however if the type variable has been unified to something introduced at a higher scope.

Levels are a somewhat mysterious technique for doing this.

See:

- <https://dl.acm.org/doi/10.1145/3729338> Practical Type Inference with Levels
- Like many things, this let-generalization is a choice not a god given thing
<https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tldi10-vytiniotis.pdf> Let Should not be Generalised
- <https://okmij.org/ftp/ML/generalization.html> How OCaml type checker works -- or what polymorphism and garbage collection have in common

I think the following union find captures some of the things here. Oleg's article mentions that levels are evocative of region based memory management. Here the levels of our union finds are indeed maintained in separate vector arenas. If we want to, we can scan the level as we pop it to do something like generalize. We also ensure when we pop a level, nothing from a higher level ever appears in the lower level tables. Still, the unions of the higher levels may transitively effect the lower level tables. It's an interesting variation of context.

Like many structured eids, it may be desirable to store the extra data not as part of the eid, but in a separate table mapping eids to their levels `levels: list[level_num]`. This is the relationship between structured eids and egg style "analyses". The difference is something like a "structure of arrays" transformation. Similar to that, I think conceptually the structured eid concept is one notch simpler and the analyses style separate table is probably more efficient.

TODO: Actually implement Hindley Milner using this thing.

```python
class EId(NamedTuple):
    level : int
    id : int

@dataclass
class LevelUF():
    levels : list[list[EId]] # a list of parent lists
    def __init__(self):
        self.levels = [[]]
    def makeset(self, level=None) -> EId:
        if level is not None:
            while len(self.levels) <= level:
                self.make_level()
        else:
            level = len(self.levels) - 1
        uf = self.levels[level]
        eid = EId(level, len(uf))
        uf.append(eid)
        return eid
    def make_level(self) -> int:
        self.levels.append([])
        return len(self.levels) - 1
    def pop_level(self):
        return self.levels.pop()
    def find(self, x : EId): # level cutoff?
        while True:
            y = self.levels[x.level][x.id]
            if x == y:
                return x
            else:
                x = y
    def union(self, x : EId, y : EId):
        x,y = self.find(x), self.find(y)
        if x != y:
            if x.level <= y.level:
                x,y = y,x
            self.levels[x.level][x.id] = y
        return y
```

```python
uf = LevelUF()
x,y,z = uf.makeset(0), uf.makeset(0), uf.makeset(1)
#uf.union(x,y)
uf.union(x,z)
uf.union(y,z)
assert uf.find(x) == uf.find(z)
uf
```

    LevelUF(levels=[[EId(level=0, id=1), EId(level=0, id=1)], [EId(level=0, id=0)]])

# Alternating Quantifier Union Find

We can combine these two union find variations by also giving constants levels they appear at.
Now a lower eid may not be unioned to a higher rigid primitive.

Basically, universal variables should not unify/equate to things at higher scope. There is something goofy about `exists x, forall y, x = y`. It collapses the model to a single entity and is not provable from base equality axioms since any other model is a countermodels. For some purposes it should be disallowed as a scope extrusion.

Lean has a related mechanism in its unification <https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html#metavariable-depth> , and so does lambda prolog and other systems that deal with quantifiers and unification.

By comparison `forall x, exists y, y = x` is not problematic in the same way and has many models for which we may be interested in a minimal one. `x` should be rigid in some sense (herbrandization / "intro" tactic).

I have wondered if this sort of scope extrusion might be a logically dignified way of modelling "disallowed" constants in e-graph extraction. Extraction probably happens at scope 0. Constants we do not want to appear in the result could be put at a larger level and then a logically correct extraction mechanism would note this.

```python
class EPrim(NamedTuple):
    level : int
    id : int

@dataclass
class QuantUF():
    levels : list[list[EId]] # a list of parent lists
    freshcounter : int = 0
    def __init__(self):
        self.levels = [[]]
    def makeset(self, level=None) -> EId:
        if level is not None:
            while len(self.levels) <= level:
                self.make_level()
        else:
            level = len(self.levels) - 1
        uf = self.levels[level]
        eid = EId(level, len(uf))
        uf.append(eid)
        return eid
    def make_level(self) -> int:
        self.levels.append([])
        return len(self.levels) - 1
    def make_eprim(self, level):
        self.freshcounter += 1
        return EPrim(level, self.freshcounter)
    def pop_level(self):
        return self.levels.pop()
    def find(self, x : EId | object):
        while True:
            if not isinstance(x, EId):
                return x
            y = self.levels[x.level][x.id]
            if x == y:
                return y
            else:
                x = y
    def resolve(self, x, y):
        assert not (isinstance(x, EId) and isinstance(y, EId))
        raise Exception("Conflict")
    def union(self, x : EId, y : EId):
        x,y = self.find(x), self.find(y)
        if x == y:
            return y
        else:
            if isinstance(x, EId) and isinstance(y, EId):
                if x.level <= y.level:
                    x,y = y,x
                self.levels[x.level][x.id] = y
                return y
            if isinstance(y, EId):
                x,y = y,x
            if isinstance(x, EId) and isinstance(y, EPrim):
                if x.level > y.level:
                    raise Exception("Scope Extrusion", x, y)
                else:
                    self.levels[x.level][x.id] = y
                    return y
            else:
                self.resolve(x,y)

```

```python
uf = QuantUF()
x,y = [uf.makeset(0) for i in range(2)]
z,w = [uf.makeset(1) for i in range(2)]
a,b = [uf.make_eprim(1) for i in range(2)]

uf.union(z,a)
uf

```

    QuantUF(levels=[[EId(level=0, id=0), EId(level=0, id=1)], [EId(level=1, id=0), EId(level=1, id=0)]], freshcounter=2)

# Bits and Bobbles

This post is part of a series of "generalized union finds"

- Poset / inequality union finds for refinement <https://www.philipzucker.com/le_find>
- Knuth Bendix / grobner / gaussian elimination as a union find <https://www.philipzucker.com/linear_grobner_egraph> <https://www.philipzucker.com/multiset_rw> It is desirable to look for stuff that is cheaper and less complicated that knuth bendix stuff. The gaussian ones are an edge case
- group / groupoid union finds <www.philipzucker.com/union-find-groupoid>, lemerre paper, Kmett talks
- semigroup / lattice / uf dict
- proof producing union finds
- backtrackable union finds
- Other examples in my EMT arxiv preprint <https://arxiv.org/abs/2504.14340>
- I'm still not 100% sure if a slotted union find makes any sense. It probably does. Yes. It's semantically strange though.

I started this blog post intending to write about "contextual union finds". Maybe I'll still do that at a later date. What I thought worked turned out to not work. Quantifier UFs are a different notion of "context" / scope.

I thought you could store a "delta union find" that holds some new unions in a sparse structure but inherits all the other unions from a parent union find. When you do find, you first find in the delta uf, then you find in the parent uf. This turns out to not be guaranteed to be canonical, at least without freezing the parent. It requires a search procedure to find the canonical root. or accepting non canonicalness until a rebuild phase (which is ok I suppose).

Another thing to write about is using union finds as keys in a dictionaries. One can do so by fully compressing them and using `min` as a tie breaker. This gives a canonical tuple representing the partition. This can be useful perhaps for hypothetical union finds that have unions that only occur under the assumption of other unions.

A Quantifier Union find + a backtracking union find is the kind of thing you'd want for unification in a lambda prolog.

A quantifier Uf shouldn't really just have integer levels becasue one could have quntifier scopes that are parallel and not nested.
`exists x, forall y, yada  /\ forall z, yada)`
So there is a tree of scopes.

You could put the occurs check into `resolve`. Or a automata minimization.

```python
@dataclass
class BackTrackUF():
    trail : list[list[int]] = field(default_factory=lambda: [[]])# things that used to be roots
    parents : list[int] = field(default_factory=list)

    def makeset(self):
        x = len(self.parents)
        self.parents.append(x)
        return x
    def pop(self):
        ps = self.trail.pop()
        for x in ps:
            self.parents[x] = x
    def push(self):
        self.trail.append([])
    def find(self, x):
        while self.parents[x] != x:
            x = self.parents[x]
        return x
    def union(self, x, y):
        x,y = self.find(x), self.find(y)
        if x != y:
            self.trail[-1].append(x)
            self.parents[x] = y
        return y

uf = BackTrackUF()
x,y,z = [uf.makeset() for _ in range(3)]
uf.push()
uf.union(x,y)
uf.push()
uf.union(y,z)
uf
```

    BackTrackUF(trail=[[], [0], [1]], parents=[1, 2, 2])

```python
uf.pop()
uf
```

    BackTrackUF(trail=[[], [0]], parents=[1, 1, 2])

Using the QuantUF to build a model for an alternating quantififer:

```python
class Q(QuantUF):
    def forall(self, lam):
        lam(self.makeprim())
    def exists(self, lam):
        l = self.makelevel()
        eid = self.makeset()
        lam(eid)

q = Q()
q.forall(lambda x: q.exists(lambda y: q.union(x, y)))


```

A regular union find is a useful thing for atomic equational "problems" like `a = b /\ b = c /\ d = e`. By "problems" I am being vague. One such problems is producing a best model (minimal / maximal) for the equations.

Constants can usually be seen as implicitly bound by an existential quantifier `exists a b c d e, a = b /\ b = c /\ d = e`.

In what sense is it a Universal? None?

`forall x y z, exists a b c d e, a = b /\ b = c /\ d = e /\ x = a`. can be solved by the primitive union find, where the `x y z` variables are considered primitives.

This can be generalized to a mixed prefix. Very often one does this by skolemizing, pushing existentials outside of the universal and adding the universal as parameters. We don't have to do this though. Implicitly everything of the lower level is a parameter.

---

title: "Context Union Finds: Keyed, Leveled, "
---

I've made it a point to accumulate union find variations.

If you forget about term structure, a fancy e-graph becomes a fancy union find. If you add term structure back in, a fancy union find becomes a fancy egraph

# Basic

A union find is a very simple thing, obscured in the article by the path compression and the tie breaking mechanisms <https://en.wikipedia.org/wiki/Disjoint-set_data_structure>

```python
class UF(Protocol):
    def find(self, x:object) -> object: ...
    def union(self, x:object, y:object) -> object: ...
    def rebuild(self) -> None: ...
    #makeset() -> Key?
    #type Key
```

```python
    def rebuild(self):
        for i in range(len(self.parents)):
            self.parents[i] = self.find(i)
```

A little usage

```python
uf = UFArena()
for i in range(10):
    uf.makeset()
uf.union(0, 1)
uf.union(1, 2)
uf.rebuild()
uf
```

    UFArena(parents=[0, 0, 0, 3, 4, 5, 6, 7, 8, 9])

Another form of the union find is instead of using integers as keys, we can allow for arbitrary objects as keys.

We can have a convention of not being in the dict as being a root or have a convention of mapping to `None` as being the root. Not being in the dict is nice in that we can be talking about some implicit infinite universe of stuff with just a small finite amount of equality added on.

```python
from dataclasses import dataclass, field

@dataclass
class UFDict():
    uf : dict[object,object] = field(default_factory=dict)
    def find(self, x):
        while x in self.uf:
            x = self.uf[x]
        return x
    def union(self, x, y):
        x,y = self.find(x), self.find(y)
        if x != y:
            self.uf[x] = y
        return y
    def rebuild(self):
        for k in self.uf.keys():
            self.uf[k] = self.find(k)
```

A different style of making a union find is using ref cells. This style makes a global view of the union find more difficult. One could do this by storing the cells in an array, but then we're back to the previous style. A garbage collector also can recollect up all the Cells.

That this is a common picture of what a union find is makes things more confusing. It is abusing too many features of the host language.

```python
from typing import Optional
class Cell():
    parent : Optional["Cell"]
    def __init__(self):
        self.parent = None
    def find(self):
        x = self
        while x.parent is not None:
            x = x.parent
        return x
    def union(self, other:"Cell"):
        x,y = self.find(), other.find()
        if x != y:
            x.parent = y
        return y
    def __eq__(self, other):
        return self.find() is other.find()

```

A little usage

```python
x,y,z = Cell(), Cell(), Cell()
x.union(y)
assert x == y
assert x != z
y.union(z)
assert x == z
```

# Context by Key

We need something like convexity to ensure that bouncing between two maps gives us a unique solution. submodularity
Scan only in between x and find(x)? Seem goofy.
Iterate only over equivalence class in higher uf.
Build entire eclass on the fly. Hmm.

We can maintain a delta union find of a layer of unions on top of some base union find. The union find is pretty forgiving

When we union, we union into a particular union find, All child union finds will immediately inherit the unions of it's parents.

We anticipate in use that the Delta's will often be sparse, so using the dictionary form makes sense (or some other sparse data structure)

I'm not convinced finding a fixed point is sufficient
maybe with full scan on union.

```python


@dataclass
class DeltaUF():
    parent_uf : UF
    duf : dict[object,object] = field(default_factory=dict)
    def find(self, x):
        #while x in self.duf:
        #    x = self.duf[x]
        #return self.parent_uf.find(x)
        while True:
            cur_x = x
            while x in self.duf:
                x = self.duf[x]
            x = self.parent_uf.find(x)
            if x == cur_x:
                return x
    def union(self, x, y):
        x,y = self.find(x), self.find(y)
        if x != y:
            if x < y:
                x,y = y,x
            self.duf[x] = y
        return y
    def rebuild(self):
        for k in self.duf.keys(): # There's some monkey business here about accidental self loops
            self.duf[k] = self.find(k)



```

0   1   2
|  \
|   \       root uf
|    \
|     \

   |\
   | \   delta

taking delta first makes us miss that root can take 2->0 so we odn't get a minimum for the eclass.
Rerooting rebuilding
We could miss stuff and fix it up to find later.

Or maintain an iterator over the eclass and search it on find

Or freeze the branches and we're only able to edit leaves

```python
# Don't support lazy deltas.
class DeltaUF():
    parent_uf : UF
    duf : dict[object,object] = field(default_factory=dict)
    def find(self, x):
        v1 = self.duf[x]
        return min([self.parent.find(v) for k,v in self.duf.items() if v == v1])
    def union(self, x, y):
        x,y = self.find(x), self.find(y)
        if x != y:
            self.duf[x] = y
        return y
    def rebuild(self):
        for k in self.duf.keys():
            self.duf[k] = self.find(k)
```

```python
uf = UFArena()

x,y,z,w = [uf.makeset() for _ in range(4)]

uf.union(x,y)
assert uf.find(x) == uf.find(y)
uf1 = DeltaUF(uf)
uf1_1 = DeltaUF(uf1)
uf1_2 = DeltaUF(uf1)

assert uf1.find(x) == uf1.find(y)
assert uf1_1.find(x) == uf1_1.find(y)
assert uf1_2.find(x) == uf1_2.find(y)

# we inherit from the parent
uf.union(z,w)
assert uf.find(z) == uf.find(w)
assert uf1.find(z) == uf1.find(w)
assert uf1_1.find(z) == uf1_1.find(w)


uf1_1.union(y,z)
#print(uf1_1)
#print(uf1_1.find(x),uf1_1.find(w))
assert uf1_1.find(x) == uf1_1.find(w)
assert uf1.find(x) != uf1.find(w)
uf1_1
```

    DeltaUF(parent_uf=DeltaUF(parent_uf=UFArena(parents=[0, 0, 2, 2]), duf={}), duf={2: 0})

DeltaUF as written is in a funny kind of way a combo of the `Cell` pointer methodology and the arena style.

Leaning into arenas everywhere, the parent_uf should be an index into a `ufs` array.

```python
class UFUniverse():
    ufs : list[UF] = field(default_factory=list)
    def make_uf(self, parents):
        if len(parents) == 0:
            uf = UFArena()
        else:


```

```python
class UFUniverse():
    root : UFArena
    dufs : DeltaUF

    def find(self, dufind, x):
        x = root.find(x)
        while True:
            dufind
        duf = dufs[dufind]
        x = duf.find(x)
        if duf.parent_uf is not None:
            dufind = duf.parent_uf
        else:
            return x
        
    def rebuild(self):
        for duf in self.dufs:
            duf.rebuild()
        self.root.rebuild()

```

# Canonizing Union Finds

A union find, similar to many data structures like dicts and sets, does not represent it's semantic meaninig in a structurally cnaonical way.

For example, one could consider a simple list as a set data structure

```python
[1,3,1,3] == [1,3]
```

    False

```python
set([1,3,1,3]) == set([1,3])
```

    True

```python
def canon_set(l):
    return tuple(sorted(set(l)))
canon_set([1,3,1,3]) == canon_set([1,3])
```

    True

Likewise for association lists as representations of mappings

```python
[(1,2), (1,2), (2,3)] == [(1,2), (2,3)]
```

    False

```python
dict([(1,2), (1,2), (2,3)]) == dict([(1,2), (2,3)])
```

    True

```python
def canon_dict(d):
    if isinstance(d,dict):
        d1 = d
    else:
        d1 = dict(d)
        assert all(v == d1[k] for k,v in d), "Not a valid mapping"
    return tuple(sorted((k,v) for k,v in d1.items()))
```

```python
canon_dict([(1,2), (1,2), (2,3)]) == canon_dict([(1,2), (2,3)])
```

    True

A union find is mostly a canonized dict but we also need to make sure that we fully rebuild / compress the uf and have a deterministic root selection method. Tie breaking by using the minimum or maximum element works

```python
def find(uf,x):
    uf1 = dict(uf)
    while x in uf1:
        x = uf1[x]
    return x

def canon_uf(uf):
    uf1 = dict(uf)


```

<https://peps.python.org/pep-0814/> frozendict pep

It's still non canonical in the sense that the eids are given out in a non det way.
That's maybe why levelled union find is interested

```python

```

```python

@dataclass(frozen=True)
class CanonUF():
    parents : tuple[int]
    
```

```python
from frozendict import frozendict
from dataclasses import dataclass
@dataclass(frozen=True)
class CanonUF():
    parents : frozendict
    def find(self, x):
        while x in self.parents:
            x = self.parents[x]
        return x
    def union(self, x, y):
        x,y = self.find(x), self.find(y)
        if x == y:
            return self
        else:
            if x < y:
                x,y = y,x
            res = []
            for k,v in self.parents:
                if 
            def find(z):
                z1 = self.find(z)
                if z1 == x:
                    return y
                else:
                    return z
            CanonUF(frozendict(for k,v in ))
```

```python
from frozendict import frozendict

@dataclass(frozen=True)
class CanonUF():
    parents : frozendict
    def __init__(self, uf):
        min_elem = {}
        for k in uf:
            min_elem[uf.find(k)] = min(min_d.get(uf.find(k), k), k)
        parents = {}
        for k in uf:
            parents[k] = min_elem[uf.find(k)]
        self.parents = frozendict(parents)
    def find(self, x):
        while x in self.parents:
            x = self.parents[x]
        return x
    

```

```python
class CanonUF():
    parents : tuple[tuple[object,object], ...]
    def __init__(self, parents):

    @staticmethod
    def empty():
        return CanonUF(parents=())
    def union(self, x, y):
        return CanonUF(parents=self.parents + ((x,y),))
    def find(self, x):
        uf1 = dict(self.parents) # could cache this. Or cache dict, and hash, but don't store.
        while x in uf1:
            x = uf1[x]
        return x
    def __eq__(self, other):
        return self.parents == other.parents
    def __hash__(self):
        return hash(self.parents)

```

Even if we fully expand without keeping base layer out separate,
we still need the union of the key uf and the

Could do it by search? yuck.
Huh. So this whole thing falls apart.
You need to scan to union. Huh. And scan both?

We could make determinsitic roots (min method)
and then hash combine the roots

([roots], frozenset(ids)) no, clashes a lot.

# Context by Levels

Using min ordering on int ids, we could consider every single eid to have a level equal to it's eid.
But i we consider object style union find instead of int arena style, it is not clear that we can always minimum compare different objects.
The level has semantic meaning.

Comparing lexicographically level then eid evokes well orderings / total orderings.
Perhaps levels could be extended to to multilevels or even eids that are nested multisets using multiset ordering. Then there is always space to place stuff. We could also use fractions as eids

If I write `let identity x = x` a type inference system should infer this as something like `identity : forall 'a, 'a -> 'a`

A general strategy of type inference is to traverse the term and generate constraints to be solved about the types of the subterms.

In the classic Hindley-Milner system, there is something called the let-generalization rule that when you enter and exit, it is a good time to actually do a little mini solve

Remy

<https://dl.acm.org/doi/10.1145/3729338> Practical Type Inference with Levels

Like many things, this let-generalization is a choice not a god given thing
<https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tldi10-vytiniotis.pdf> Let Should not be Generalised

<https://okmij.org/ftp/ML/generalization.html> How OCaml type checker works -- or what polymorphism and garbage collection have in common

a structured eid is (level, int) pairs telling us which union find to go into.

```python

```

    UF(uf=[2, 2, 2, 3, 4, 5, 6, 7, 8, 9])

Does the level uf work but DiffUF doesn't? eid belonging to levels fixes the issue before where we need to loop `find`?

Hmm. what if genericity lived at the Tree level instead of in TypeVar...

Hmm. Level UF doesn't get non interference at all really.
I guess it inherits from upper levels, and we can delete lower levels someday and only retain their implicit influence.

Is a level union find easier to backtrack? No not really.

```python
type EId = tuple[int,int] # level, index
@dataclass
class LevelUF():
    levels : list[list[EId]] # use dict union find because probably sparse
    def __init__(self):
        self.levels = [[]]
    def makeset(self, level=None) -> EId:
        if level is not None:
            while len(self.levels) <= level:
                self.make_level()
        else:
            level = len(self.levels) - 1
        uf = self.levels[level]
        eid = (level, len(uf))
        uf.append(eid)
        return eid
    def make_level(self) -> int:
        self.levels.append([])
        return len(self.levels) - 1
    def find(self, x : EId): # level cutoff?
        level, key = x
        while True:
            level, key = x
            y = self.levels[level][key]
            if x == y:
                return x
            else:
                x = y
    def union(self, x : EId, y : EId):
        x,y = self.find(x), self.find(y)
        if x != y:
            if x[0] <= y[0]:
                x,y = y,x
            self.levels[x[0]][x[1]] = y
        return y

uf = LevelUF()
x,y,z = uf.makeset(0), uf.makeset(0), uf.makeset(1)
#uf.union(x,y)
uf.union(x,z)
uf.union(y,z)
uf
```

    LevelUF(levels=[[(0, 1), (0, 1)], [(0, 0)]])

Interspersing leveled atom intern tables.
atoms : list[list[str]] # a / 1    fresh consts.  in scope

forall atoms0, exists eid0, forall atoms1, exists eid2, /\ /\ a = e /\ e1 = e2 /\  as a question. If we skolemize it becomes unification-ish?
levels counting up like de bruijn?

```python
uf = LevelUF()

x,w = [uf.makeset() for _ in range(2)]
y,z = [uf.makeset(1) for _ in range(2)]

uf.union(x,y)
assert uf.find(x) == uf.find(y)

uf.union(z,w)
assert uf.find(z) == uf.find(w)

uf.union(y,z)

assert uf.find(x) == uf.find(w)
uf
```

    LevelUF(levels=[[(0, 0), (0, 0)], [(0, 0), (0, 1)]])

```python
class LevelUF():
    base : list[int]
    levels : list[dict[int, int]] # use dict union find because probably sparse
    def makeset(self):
        eid = len(self.base)
        self.base.append(eid)
        return eid
    def find(self, level, x):
        while level >= 0:
            uf = self.levels[level]
            while x in uf:
                x = uf[x]
            level -= 1
        while self.base[x] != x:
            x = self.base[x]
        return x
    def union(self, levelx, x, levely, y): # two levels?
        if levelx < levely: # ensure levelx is the higher level
            levelx, x, levely, y = levely, y, levelx, x
        x,y = self.find(levelx, x), self.find(levely, y)
        if x != y:
            if levelx == -1:
                self.base[x] = y
            else:
                self.levels[levelx][x] = y
```

```python
class QuantAltUF():
    fresh : int
    foralls : list[set]
    exists : list[dict]
    """
    Things happening in prefixes forall x, exists y, forall z, ...
    exists y, forall x, exists z, z = y  should point z to y, not vice versa.
    """
    def makeset(self, level):
        eid = self.fresh
        self.fresh += 1
        self.exists[level][eid] = eid
        return eid
    def gensym(self, level):
        eid = self.fresh
        self.fresh += 1
        self.foralls[level].add(eid)
        return eid



```

This is kind of prefix normal form coded. What about telescope?

<https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html#metavariable-depth>
The idea that you can only union lower vars to higher vars

If you took the "primitive union find"
That has rigid atoms p,q,r  and unionable atoms a,b,c
The rigid have to win.
If you stratify this into layers of interspersing p,q,r and a,b,c, then you get

Hmm. But then when I call makeset, the variable needs to belong to that level... so i guess this is a different concept

let generalization and levels in hindley milner inference.

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

<https://usr.lmf.cnrs.fr/~jcf/publis/puf-wml07.pdf>  A Persistent Union-Find Data Structure

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

```python
@dataclass
def UFUnion():
    ufs : list[UF] = field(default_factory=list)
    def find(self, x:object) -> object:
        while True:
            cur_x = x
            for uf in self.ufs:
                x = uf.find(x)
            if x == cur_x:
                return x
```

# Persistent

<https://github.com/MagicStack/immutables>
<https://github.com/tobgu/pyrsistent>
<https://discuss.python.org/t/pep-603-adding-a-frozenmap-type-to-collections/2318/219>
frozendict <https://pypi.org/project/frozendict/>

```python
! python3 -m pip install immutables
```

    Collecting immutables
      Downloading immutables-0.21-cp312-cp312-manylinux_2_5_x86_64.manylinux1_x86_64.manylinux_2_17_x86_64.manylinux2014_x86_64.whl.metadata (4.5 kB)
    Downloading immutables-0.21-cp312-cp312-manylinux_2_5_x86_64.manylinux1_x86_64.manylinux_2_17_x86_64.manylinux2014_x86_64.whl (104 kB)
    Installing collected packages: immutables
    Successfully installed immutables-0.21

```python
from immutables import Map
d = Map()
d1 = d.set(1,2)
for x in d1.items():
    print(x)

```

    (1, 2)

```python
! python3 -m pip install pyrsistent
```

    Collecting pyrsistent
      Downloading pyrsistent-0.20.0-cp312-cp312-manylinux_2_17_x86_64.manylinux2014_x86_64.whl.metadata (27 kB)
    Downloading pyrsistent-0.20.0-cp312-cp312-manylinux_2_17_x86_64.manylinux2014_x86_64.whl (122 kB)
    Installing collected packages: pyrsistent
    Successfully installed pyrsistent-0.20.0

```python
from pyrsistent import pmap
d = pmap()
d1 = d.set(1,2)
for x in d1.items():
    print(x)
```

    (1, 2)

```python
d = {}
d.set(1,2)
```

    ---------------------------------------------------------------------------

    AttributeError                            Traceback (most recent call last)

    Cell In[16], line 2
          1 d = {}
    ----> 2 d.set(1,2)


    AttributeError: 'dict' object has no attribute 'set'

# Bits and Bobbles

I called it base. Are fibers leaking into my thinking?

I have meet and join of uf. A heyting algerba if I can define an A => B? Probably the finest partition that when merged with A gives B or is less than B? C /\ A  <= B

def diff(self, other):

![](https://en.wikipedia.org/wiki/File:Set_partitions_4;_Hasse;_circles.svg) partition refinement <https://en.wikipedia.org/wiki/Partition_of_a_set>

## Primitive UF using Cells

```python
from typing import Optional
class Cell():
    parent : Optional["object | Cell"]
    def __init__(self):
        self.parent = None
    def find(self):
        x = self
        while x.parent is not None and isinstance(x.parent, Cell):
            x = x.parent
        return x
    def union(self, other:"Cell"):
        x,y = self.find(), other.find()
        if x == y:
            return y
        if x != y and isinstance(x, Cell):
            x.parent = y
        elif x != y and isinstance(y, Cell):
            y.parent = x
        elif x != y:
            raise Exception("Cannot union two different non-cells")
    def __eq__(self, other):
        if isinstance(other, Cell):
            y = other.find()
        return self.find() is other.find()
    def ground(self, value):
        x = self.find()

x,y,z = Cell(), Cell(), Cell()
x.union(y)
assert x == y
assert x != z
y.union(z)
assert x == z
z.ground(42)
assert
```

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
Hmm. Maybe this is why z3 does it this way. For fast backtracking <https://z3prover.github.io/papers/z3internals.html#sec-equality-and-uninterpreted-functions>

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
<https://en.wikipedia.org/wiki/Kruskal%27s_algorithm>

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
