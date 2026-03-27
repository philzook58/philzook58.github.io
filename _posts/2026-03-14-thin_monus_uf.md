---
title: "Monus, Factor, and Thinning Union Finds"
date: 2026-03-14
---

I have kind of a recipe book I follow to thinking about generalized e-graphs or e-graph modulo theories. One recipe is to try and swap a regular union find out with some notion of generalized union find.

[Last time](https://www.philipzucker.com/thin1/) I discussed what a thinning is.

- A thinning is a recipe on how to extract a sublist from another
- A thinning is useful as a compact representation of many de Bruijn Index shifts

I believe baking thinnings into a union find bakes in some de bruijn index manipulation, helping to support an alpha invariant e-graph. I think this is quite similar to a slotted e-graph, but ignoring the permutation aspect and focusing on the redundancy aspect.

Along the way though there are some union find variants I had never thought of before which are more elementary and interesting in their own right. They all have annotations along the edges and none of these annotations form a group.

Here we go!

# Union Find

A regular union find is a tree where the children point up to their parents. Because of this, it is easy to glue one tree to another when you want them to merge and because the children lazily chase their parents, they discover they now belong in the same partition without needing the eagerly update everything. Pretty cool!

At this point, my minimal union find has become pretty consistent and just flies out of my fingers.

```python
from dataclasses import dataclass, field
type Id = int
@dataclass
class UF:
    parents : list[Id] = field(default_factory=list)
    def makeset(self):
        # make a new identifier
        i = len(self.parents)
        self.parents.append(i)
        return i
    def find(self, x : Id) -> Id:
        # Get canonical identifier for x
        while True:
            y = self.parents[x]
            if y == x:
                return x
            x = y
    def union(self, x : Id, y : Id) -> Id | None:
        # assert that x and y are "equal" in some sense.
        x = self.find(x)
        y = self.find(y)
        if x != y:
            self.parents[x] = y
            return y
        else:
            return None

uf = UF()
a = uf.makeset()
b = uf.makeset()
c = uf.makeset()
assert uf.find(a) != uf.find(b)
uf.union(a,b)
assert uf.find(a) == uf.find(b)
assert uf.find(a) != uf.find(c)
uf.union(b,c)
assert uf.find(a) == uf.find(c)
uf
```

    UF(parents=[1, 2, 2])

# Offset Union Find

One may want to add extra information in the union find, either on the edges, on the nodes, or on the roots / classes.

One thing you can do at little cost is express offset relationships like `x + 3 = y - 4`. The offset values are concrete values whereas `x` and `y` can be unspecified identifiers of the union find. We can do this by adding an offset annotation to the `parents` table and collecting up the offsets as we traverse up the tree.

```python
from dataclasses import dataclass, field
type Id = tuple[int, int] # offset and id
@dataclass
class OffsetUF:
    parents : list[Id] = field(default_factory=list)
    def makeset(self) -> Id:
        i = len(self.parents)
        self.parents.append((0,i))
        return (0,i)
    def find(self, x : Id) -> Id:
        off, xid = x
        while True:
            (offy, yid) = self.parents[xid]
            if yid == xid:
                assert offy == 0
                return (off, xid)
            off += offy
            xid = yid
    def union(self, x : Id, y : Id) -> Id | None:
        (offx, xid) = self.find(x)
        (offy, yid) = self.find(y)
        if xid != yid:
            z = (offy - offx, yid)
            self.parents[xid] = z
            return z
        else:
            return None
def add(off, x : Id) -> Id:
    return (off + x[0], x[1])
uf = OffsetUF()
x = uf.makeset()
y = uf.makeset()
uf.union(add(3, x), add(4, y))
uf
```

    OffsetUF(parents=[(1, 1), (0, 1)])

Basically this entirely generalizes to at least any annotation that has an appropriate notion of `0`, `+=`, and `-`. A Group fits the bill. Other examples of groups are invertible matrices, +- parity, cyclic groups, permutations groups, and more.

I first heard of this concept from talks by Ed Kmett, but it floats around:

- <https://www.philipzucker.com/union-find-groupoid/>
- <https://byorgey.github.io/blog/posts/2024/11/02/UnionFind.html> <https://byorgey.github.io/blog/posts/2024/11/18/UnionFind-sols.html>
- <https://dl.acm.org/doi/10.1145/3729298> Relational Abstractions Based on Labeled Union-Find
- <https://exia.informatik.uni-ulm.de/fruehwirth/constraint-handling-rules-book.html> Chapter 10
- <https://leodemoura.github.io/files/oregon08.pdf> Slide 167
- Sofia B pointed out <https://link.springer.com/chapter/10.1007/978-3-540-39813-4_5> Congruence Closure with Integer Offsets

# Positive Offset / Monus Union Find

A slight but interesting twist is to require the offset annotations be only positive. To achieve this, the annotations now need control of the direction `union` adds to the parents table.

```python
from dataclasses import dataclass, field
type Id = tuple[int, int] # offset and id
@dataclass
class PosOffsetUF:
    parents : list[Id] = field(default_factory=list)
    def makeset(self) -> Id:
        i = len(self.parents)
        self.parents.append((0,i))
        return (0,i)
    def find(self, x : Id) -> Id:
        off, xid = x
        while True:
            (offy, yid) = self.parents[xid]
            if yid == xid:
                assert offy == 0
                return (off, xid)
            off += offy
            xid = yid
    def union(self, x : Id, y : Id) -> Id | None:
        (offx, xid) = self.find(x)
        (offy, yid) = self.find(y)
        if xid != yid:
            if offy >= offx:
                z = (offy - offx, yid)
                self.parents[xid] = z
            elif offx > offy:
                z = (offx - offy, xid)
                self.parents[yid] = z
            return z
        else:
            return None
def add(off, x : Id) -> Id:
    return (off + x[0], x[1])
uf = PosOffsetUF()
x = uf.makeset()
y = uf.makeset()
uf.union(add(4, x), add(3, y))
uf
```

    PosOffsetUF(parents=[(0, 0), (1, 0)])

This is quite remarkable to me because positive offset feels a bit more to me like an inequality that supports the nice interface and performance of the union find. It is unusual in this respect though.

Positive offsets form a [monus](https://en.wikipedia.org/wiki/Monus). <https://doisinkidney.com/posts/2026-03-03-monus-heaps.html> One wonders if one just points those heap edges upwards if you get union finds? Other examples of monus include probability factors <https://hackage.haskell.org/package/monus-weighted-search-0.1.0.0> `0 <= P <= 1` which is kind of logarithmically related to the offset union find. This should also work.

# Factor Union Find

A slight twist on the above is to consider multiplication by integer constants `6*x = 4*y`. Because again we don't insist on turning this into a group, it isn't clear we can derive a solution in the form `x = ?a * y` or `y = ?b * x` without constraining more than is implied by the assertion. Nevertheless there is a "best" solution if we create a new identifier `x = 2*z`, `y = 3*z`. These number come out of considerations of the prime factorization / least common multiple. The right had side says there must be at least 2 factors of 2, but `6` only has 1 factor, so we must pull another 2 out of `x`. Likewise we must pull a factor of `3` out of y.

In short, union not only controls the directionality of parent, it also must sometimes generate a fresh id.

```python
from dataclasses import dataclass, field
import math
type Id = tuple[int, int] # multiplier and id
@dataclass
class MulUF:
    parents : list[Id] = field(default_factory=list)
    def makeset(self) -> Id:
        i = len(self.parents)
        self.parents.append((1,i))
        return (1,i)
    def find(self, x : Id) -> Id:
        mx, xid = x
        while True:
            (my, yid) = self.parents[xid]
            if yid == xid:
                assert my == 1
                return (mx, xid)
            mx *= my
            xid = yid
    def union(self, x : Id, y : Id) -> Id | None:
        (mx, xid) = self.find(x)
        (my, yid) = self.find(y)
        if xid != yid:
            mz = math.lcm(mx,my)
            if mz == mx:
                z = (mx // my, x)
                self.parents[yid] = z
                return z
            elif mz == mx:
                z = (my // mx, y)
                self.parents[xid] = z
                return z
            else:
                (_, zid) = uf.makeset()
                self.parents[xid] = (mz // mx, zid) 
                self.parents[yid] = (mz // my, zid)
                return (mz, zid)
        else:
            assert mx == my
            return None
def mul(m, x : Id) -> Id:
    return (m * x[0], x[1])
uf = MulUF()
x = uf.makeset()
y = uf.makeset()
uf.union(mul(6, x), mul(4, y))
uf
```

    MulUF(parents=[(2, 2), (3, 2), (1, 2)])

This generalizes to things that have the appropriate notions of least common multiple or factoring. Perhaps something in the ballpark of <https://en.wikipedia.org/wiki/Principal_ideal_domain> . Polynomials are also interesting things to factor.

<https://en.wikipedia.org/wiki/Factorization>

A similar thing can be done with single variable string / word equations like `abaX = abY`. The structured eids in this case would be a tuple of `(prefix, eid, postfix)`
<https://en.wikipedia.org/wiki/Monoid_factorisation>

"Vectorizing" the offset union find gives you multiset labels (A multiset is labeled positive counts). Like in the factor union find, you now sometimes have to produce new eids. The interpretation is that one is asserting equations between expressions with a single unknown multiset `{a,a,b} U X = {a,c,d} U Y` would have a "solution" `X = {c,d} U Z`, `Y = {a,b} U Z`

# Thinning Union Find

To repeat, thinnings are bitvectors that represent monotonic mappings of this form.

![](/assets/thinning/thinning.png)

A thinning union find is a relative to all the above, but has it's own slight twists. I kind of think of it as a data structure for solving unknown thinning unification problems of the form `t1 . X = t2 . Y` or thinning action equations of the form `t1 * X = t2 * Y`, the difference being whether we consider X and Y to be variables representing unknown thinnings or unknown things thinnings are acting on (like terms with context).

When we need to reconcile two thinnings, we kind of know that the only inputs that are actually being used are those inputs used by both. This is the simple bitwise and of the thinning bitvectors. It corresponds to the least common multiple calculation in the factor union find above if you think about it.

This notion appears in the slotted union find as redundancies as Rudi has shown me.

This is also a notion of thinning division. Sometimes you can find a thinning `t . X = s` which makes `X` kind of the divisor of `s / t`.

With these two pieces we can follow our noses according to the factor union find and do basically the same thing, just being a little more careful about the order of multiplication/composition.

```python
type Thin = list[bool]
def dom(f : Thin): # domain is big side
    return len(f)
def cod(f : Thin): # codomain is small side
    return sum(f)
# The action on contexts and terms
# f(t)    widens t
# (ctx)f  thins a context
def comp(f : Thin, g : Thin) -> Thin:
    assert cod(f) == dom(g)
    i = 0 
    result = []
    for a in f:
        if a:
            result.append(g[i])
            i += 1
        else:
            result.append(False)
    assert i == len(g)
    return result   

def lcm(f : Thin, g : Thin) -> Thin:
    assert len(f) == len(g)
    return [a and b for a,b in zip(f,g)]

def div(f : Thin, g : Thin) -> Thin:
    assert dom(f) == dom(g)
    assert all(not a for a,b in zip(f,g) if not b) # f is thinner than g
    return [a for a,b in zip(f,g) if b]
# comp(div(lcm(f,g), g), g) == f

type Id = tuple[Thin, int]
@dataclass
class ThinUF:
    parents : list[Id] = field(default_factory=list)
    def makeset(self, scope : int) -> Id:
        i = len(self.parents)
        id = ([True]*scope, i)
        self.parents.append(id)
        return id
    def find(self, x : Id) -> Id:
        thin, xid = x
        while True:
            (thiny, yid) = self.parents[xid]
            if xid == yid:
                assert all(thiny)
                return (thin, xid)
            thin = comp(thiny, thin)
            xid = yid
    def union(self, x : Id, y : Id) -> Id | None:
        thinx, xid = self.find(x)
        thiny, yid = self.find(y)
        if xid != yid or thinx != thiny:
            thinz = lcm(thinx,thiny)
            (_, z) = self.makeset(cod(thinz))
            self.parents[xid] = (div(thinz,thinx), z)
            self.parents[yid] = (div(thinz,thiny), z)
            return (thinz, z)
        else:
            # hmm
            return None

def widen(thin : Thin, x : Id):
    thinx, xid = x
    return (comp(thin,thinx), xid)
uf = ThinUF()
a = uf.makeset(2)
b = uf.makeset(2)
uf.union(widen([True, False, True], a), widen([False, True, True], b))
uf

```

    ThinUF(parents=[([False, True], 2), ([False, True], 2), ([True], 2)])

# Bits and Bobbles

Rudi has a pitch about semigroups with involution as being the generalization. I do not know if the above examples are semigroups with involutions.

The thinning union find is more of a category action rather than a group or groupoid action. <https://ncatlab.org/nlab/show/action+of+a+category+on+a+set> for a category with pullbacks?

Mcbride mentioned an analogy to thinning manipulations as euclids algorithm. <https://types.pl/@pigworker/116166766060828508> I think this is similar to the above analogy between the factor union find and thinning union find, but asking a slightly different problem.

Reed Mullanix also made some interesting observations and connections to strings and monus here <https://types.pl/@totbwf/116167359953764857>

More union find variations:

- <https://www.philipzucker.com/weighted_uf/> The weigted union find has information associated with nodes, not roots, in a manner which controls the union direction.
- <https://www.philipzucker.com/prim_level_uf/> scoped union finds so you can blow away chunks
- <https://www.philipzucker.com/context_uf2/> a notion of contextual union find, union under hypotheses
- Other examples in my EMT arxiv preprint <https://arxiv.org/abs/2504.14340>
- Poset / inequality union finds for refinement <https://www.philipzucker.com/le_find>
- Knuth Bendix / grobner / gaussian elimination as a union find <https://www.philipzucker.com/linear_grobner_egraph> <https://www.philipzucker.com/multiset_rw> It is desirable to look for stuff that is cheaper and less complicated that knuth bendix stuff. The gaussian ones are an edge case
- group / groupoid union finds <www.philipzucker.com/union-find-groupoid> , lemerre paper, Kmett talks
- One can also have lattice annotations associative with roots like egg analyses. Probably something more general than lattice is possible, because "count" is a perfectly reasonable annotation that is not a lattice.

It feels to me like there is a difference in considering the union find annotations to be "rigid" / injective / constructors vs, not. Rigid annotations feel like E-unificiation, flexible annotations feel like ground E-completion. This post was all about rigid annotations. The linear, grobner, and multiset completion feel like E-completion.

Unification has a categorical explanation in terms of pullbacks

- <https://www.cs.bu.edu/fac/snyder/publications/UnifChapter.pdf> 3.3.3
- <https://www.cs.man.ac.uk/~david/categories/book/book.pdf> pg 173 Burstall and Rydeheard
- <https://www.sciencedirect.com/science/chapter/edited-volume/abs/pii/B9780120463701500127>  6 - What Is Unification?: A Categorical View of Substitution, Equation and Solution - Goguen

# Value / Constructor Union Find

Another interesting class of union finds comes from considering structured eids that can be constructors.
A union find is useful and related to the process of unification.
A more ground entity needs to become the parent of a variable, not the other way around.
Here is a union find that supports concrete strings and unknowns.

We can also have something more familiar looking with Nil and Cons nodes.

```python
from dataclasses import dataclass, field
@dataclass
class Nil:
    pass
@dataclass
class Cons:
    car : "Id"
    cdr : "Id"

type Id = int | Cons | Nil

@dataclass
class ListUF:
    parents : list[Id] = field(default_factory=list)
    def makeset(self):
        i = len(self.parents)
        self.parents.append(i)
        return i
    def find(self, x : Id) -> Id:
        while True:
            if not isinstance(x,int):
                match x:
                    case Cons(car, cdr):
                        return Cons(self.find(car), self.find(cdr))
                    case Nil():
                        return Nil()
                    case _:
                        raise Exception("Invalid id", x)
            y = self.parents[x]
            if y == x:
                return x
            x = y
    def union(self, x : Id, y : Id) -> Id | None:
        x = self.find(x)
        y = self.find(y)
        if x != y:
            if not isinstance(x,int) and not isinstance(y, int):
                match x,y:
                    case Cons(car, cdr), Cons(car2, cdr2):
                        a = self.union(car, car2)
                        b = self.union(cdr, cdr2)
                        return Cons(car if a is None else a, cdr if b is None else b)
                    case Nil(), Nil():
                        return None
                    case _:
                        raise Exception("Incompatible union", x, y)
                    
            if isinstance(x, int):
                z = y
                self.parents[x] = y
            elif isinstance(y, int):
                z = z
                self.parents[y] = x
            return z
        else:
            return None
    
uf = ListUF()
a = uf.makeset()
b = uf.makeset()
c = uf.makeset()
d = uf.makeset()
uf.union(a, Cons(c, Nil()))
uf.union(b, Cons(c, Nil())) # hmm. actually a = b could propagate.
assert uf.find(a) == uf.find(b)
```

The Nat version of this with Succ and Zero constructors is very similar to the positive offset union find.

```python
from dataclasses import dataclass, field
type Id = int | str
@dataclass
class ValueUF:
    parents : list[Id] = field(default_factory=list)
    def makeset(self):
        i = len(self.parents)
        self.parents.append(i)
        return i
    def find(self, x : Id) -> Id:
        while True:
            if isinstance(x,str):
                return x
            y = self.parents[x]
            if y == x:
                return x
            x = y
    def union(self, x : Id, y : Id) -> Id | None:
        x = self.find(x)
        y = self.find(y)
        if x != y:
            if isinstance(x,str) and isinstance(y, str):
                raise Exception("Incompatible union", x, y)
            elif isinstance(x, str):
                z = x
                self.parents[y] = z
            elif isinstance(y, str):
                z = y
                self.parents[x] = z
            return z
        else:
            return None

uf = ValueUF()
a = uf.makeset()
b = uf.makeset()
c = uf.makeset()
uf.union(a, "foo")
uf.union(a,b)
assert uf.find(b) == "foo"
uf.union(b,c)
uf
```

# Babbling

`T1 . X . T3 = T2 . Y . T4` double sided action could also be supported without much change. The above examples we too commutative to discuss this.

Having multiple variables on each side kind of kicks up the complexity of doing the thing. It becomes more like a word equation rather than a union find. Two variable word equations have better behavior so maybe there is something there.

A generalization of this idea is making a union find in any category with pullbacks. If we have some unkown morphisms X and Y, but learn that `X . f = Y . g`, we can refine X and Y to and unknown Z compose with edges of the pullback square.

Thinning division is somewhere in the ballpark of retracts in categroy theory

Consider lists. If mystery list a is related to mystery list b because they are both specified thinnings of c.
T [a,b,c,d] = X
T2 [a,b,c,d] = Y
Q = W X  
Q = W Y
This would just supply constraints on X and Y values where they both have opinions

But Q is kind of not a fixed thing. It's fixed holes into which arbitrary stuff can be places. A routing system

[0,1,2,3] = W1 (W2 Z) X is unknown list

W W1
W W3
The ids should represent unknown thinnings themselves?
So more like a value uf where X may become a concrete thinning rather than annotation

W . X = W2 . Y ==> exists Z, (W & W2) . Z = W . X = W2 . Y

The bitwise and of the thinning representation

If we specify the lists are [0,1,2,3,4] kind of. This is exactly getting at alpha invarinace.

So this is kind of a generlization of an atomic union find where values are v0, v1, v3. This requires we thin to 1, but maybe we shouldn't. In context free case, there can only be value... ?
Forests of substitutions not terms.
Is this atomic type theory?

Ok so eids are also morphisms in the category, and annotation is composition onto a specified morphism
f. ?x = g . ?y
This is the edges of a square. Shit. That is a pullback.
eids aren't objects. They are morphisms.
The action perspective is partial composition with
I don't know that this subsumes the group action case.
It does work for monus. The eids were unknown positive integers. And for multiplication

Yes for the grup uf, we could interpret the eids as unknown group elements. We are then determinating the relationship of these elements to each other, until perhaps we ground them to specific g.

Well, we could suppose we have an unknown object too, but this is strange.
It's more of a category action. <https://ncatlab.org/nlab/show/action+of+a+category+on+a+set> for a category with pullbacks

Try rereading category theory section of unification review

Egraphs as unifications, as unification state?

Omelets need onions
My posts
Union Find Abstract Interpretation
de Moura Slides

Structured eid are an ephemeral part and an interned part
The ephemeral part still could have rewriting applied to it, or be unlocked to further something by being inserted into a new context.
This is similar to the Value Neutral distinction of NbE perhaps.

We could say we want the order of the `union` asserted to not change the semantic meaning of the result. Duplicate union assertions also shouldn't matter.

Note that in the offset union find we assume that two elements should never be related by two different offsets. This is possible however in other sitautions, in which case you may need to also store group symmetries like in the slotted union find.

Positive offsets form a monus. <https://doisinkidney.com/posts/2026-03-03-monus-heaps.html> One wonders if one just points those heap edges upwards if you get union finds?

type Thin = list[bool]

def meet(t1, t2):
    assert len(t1) == len(t2), "meet: thin sources differ"
    return [a and b for a,b in zip(t1,t2)]
