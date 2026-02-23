---
title: An Associative-Commutative (AC) Hash Cons with AC matching
date: 2026-02-22
---

There is an approach to problem solving where you take simpler and simpler subproblems until they are quite obvious, and then you build back up to the thing you want.

People want an egraph that supports associativity and commutativty without blowing up.

A step in that direction is to look at what an AC hash cons looks like

These are other steps towards that goal:

- <https://www.philipzucker.com/weighted_uf/>. Weighted union find + hash cons = ground knuth bendix
- <https://www.philipzucker.com/subterm_mod_miller/> What is subterms modulo AC?

# Two Kinds of Nodes

One node is a regular ordered children node and the other is one where only the multiset of children is relevant. A simple way of implementing multisets is to use tuples where you only cosntruct them in sorted form.

```python
from dataclasses import dataclass, field

type Id = int # Integer identitfiers for hashconsed nodes

@dataclass(frozen=True)
class App:
    f : str
    args : tuple[Id, ...]

@dataclass(frozen=True)
class ACApp:
    f : str
    args : tuple[Id, ...]
type Node = App | ACApp
```

This is very similar to the notion of "containers". It can also be thought of as an adt

```ocaml
type term =
    | App of term list
    | ACApp of term multiset
    | PolyApp of term poly
    | SetApp of term set
    | ...
```

# AC Hash Consing

The flattened sorted form of an AC symbol is a normal form.

Smart constructors can do this flattening and sorting. Because we can assume inductviely that things are already flattened, we don't have to do a deep search

```python
@dataclass
class ACHashCons:
    memo : dict[Node, Id] = field(default_factory=dict) # IndexMap
    nodes : dict[Id, Node] = field(default_factory=dict)

    def mk_node(self, node : Node) -> Id:
        if node in self.memo:
            return self.memo[node]
        else:
            id = len(self.nodes)
            self.nodes[id] = node
            self.memo[node] = id
            return id

    def mk_app(self, f : str, args : tuple[Id, ...]) -> Id:
        return self.mk_node(App(f, args))


    def mk_acapp(self, f : str, args : tuple[Id, ...]) -> Id:
        # immediate smart constructor flattening
        flatargs = [] 
        for id in args:
            assert isinstance(id, int)
            n = self.nodes[id]
            if isinstance(n, ACApp) and n.f == f:
                flatargs.extend(n.args)
            else:
                flatargs.append(id)
        flatargs.sort()
        return self.mk_node(ACApp(f, tuple(flatargs)))

hc = ACHashCons()
a = hc.mk_app("a", ())
b = hc.mk_app("b", ())
pab = hc.mk_acapp("+", (a, b))
pba = hc.mk_acapp("+", (b, a))
assert pab == pba
pbb = hc.mk_acapp("+", (b, b))
pabb = hc.mk_acapp("+", (pab, b))
pbba = hc.mk_acapp("+", (pbb, a))
 
assert pabb == pbba
assert len(hc.nodes[pabb].args) == 3

pabb2 = hc.mk_acapp("+", (a, b, b)) # We don't have to make the intermediate nodes
assert pabb == pabb2
```

We don't have to make AC symbols two operands at a time. It may be better to only construct the ACNode one you have all it's children.

The main time one wants to intern an AC symbol is when it is "sealed off" by being under a new symbol like `f(a + b + c)`. Otherwise it may be better to keep the AC thing ephemeral like in `ACId` (see below).

# AC Matching

AC matching does require search and can return multiple matching substitutions.

First a simple language of patterns

```python
@dataclass(frozen=True)
class Var:
    name : str

@dataclass(frozen=True)
class PApp:
    f : str
    args : tuple['Pattern', ...]

@dataclass(frozen=True)
class PACApp:
    f : str
    args : tuple['Pattern', ...]

type Pattern = Var | PApp | PACApp

```

Then we implement the thing itself. At each AC node we need to enumerate all ways of splitting the children into partitions

A brute force way of doing so is this

```python
import itertools
def partitions(s, n):
    for assign in itertools.product(range(n), repeat=len(s)):
        bins = [[] for _ in range(n)]
        for x,b in zip(s, assign):
            bins[b].append(x)
        if all(bin for bin in bins):
            yield tuple(tuple(bin) for bin in bins)

list(partitions("abc", 2))
```

    [(('a', 'b'), ('c',)),
     (('a', 'c'), ('b',)),
     (('a',), ('b', 'c')),
     (('b', 'c'), ('a',)),
     (('b',), ('a', 'c')),
     (('c',), ('a', 'b'))]

## Mixing Ephemeral and Interned Terms

It is useful to consider if you want multiple representations of terms. You may want a way to have both ephemeral and interned terms or multiple levels of interning. ACId is kind of a like an uninterned AC node. We produce these things ephemerally during matching and I think it's kind of useful and interesting to have them.

```python
from dataclasses import dataclass,field
import itertools
type Id = int

@dataclass(frozen=True)
class ACId:
    f : str
    args : tuple[Id, ...]

type SId = Id | ACId # structured Ids. ACApp may be uninterned / ephemeral
# obviously it hurts to keep making copies of the same struct, but they are noticeably different
```

This paper about the Kontroli term representation talks about long lived and short lived terms <https://dl.acm.org/doi/10.1145/3573105.3575686> . I also mentioned it in my omelets need onions paper <https://arxiv.org/abs/2504.14340> . Chris also mentioned usage of "scoped hash conses" <https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/codegen/src/scoped_hash_map.rs> in the cranelift compiler.

# Doing the matching

Inspired by [Max's nice version of ematching](https://github.com/mwillsey/microegg). There is some similarity between ematching in an egraph and ac-matching. They are both search based with an obvious finite thing to search out of. I pointed out this similarity here <https://www.philipzucker.com/relational-ac-matching/> where I wondered if AC is as good a fit to the relational idea as ematching is.

Basically you traverse down the pattern. You need to try all partitions of the arguments when you hit an AC pattern.

```python
def acmatch_rec(hc : ACHashCons, p : Pattern, id : SId, subst) -> list[dict[str, SId]]:
    if isinstance(id, ACId):
        n = id
    else:
        n = hc.nodes[id]
        if isinstance(n, ACApp): # normalize into ACId to simplify logic below
            n = ACId(n.f, n.args) # could move this below Var for efficiency, but whatev
    match p, n:
        case Var(x), _:
            # If variable check if binding is consistent
            if x in subst:
                if subst[x] == id: # something smarter for ACId?
                    return [subst]
                else:
                    return []
            else:
                newsubst = subst.copy()
                newsubst[x] = id
                return [newsubst]
        case PApp(pf, pargs), App(f, args) if pf == f and len(pargs) == len(args):
            substs = [subst]
            for parg, arg in zip(pargs, args):
                substs = [subst for subst0 in substs for subst in acmatch_rec(hc,parg, arg, subst0)]
            return substs
        case PACApp(pf, pargs), ACId(f, args) if pf == f:
            # we need to hand down temporary ACNodes
            # What about ACNode with 1 element? ACI easier?
            res = []
            # enumerating partitions more lazily would prune earlier.
            # I suppose the binary form of normal form of ac would do this for free...
            # No. Just _don't_  flatten your patterns.
            for subargs in partitions(args, len(pargs)):
                # We consider singleton usage +(a) to be the identity `plus(a) = a`
                subargs = map(lambda a: ACId(f, a) if len(a) > 1 else a[0], subargs)
                substs = [subst]
                for parg, arg in zip(pargs, subargs):
                    substs = [subst for subst0 in substs for subst in acmatch_rec(hc, parg, arg, subst0)]
                res.extend(substs)
            return res
        case _:
            return []

    
def acmatch(hc : ACHashCons, p : Pattern, id : Id) -> list[dict[str, Id]]:
    return acmatch_rec(hc, p, id, {})
```

Some example output

```python
hc = ACHashCons()
a = hc.mk_app("a", ()) # id 0
b = hc.mk_app("b", ()) # id 1
c = hc.mk_app("c", ()) # id 2
pabc = hc.mk_acapp("+", (a, b, c)) # id 3
fa  = hc.mk_app("f", (a,)) # id 4
ffa = hc.mk_app("f", (fa,)) # id 5
paab = hc.mk_acapp("+", (a, a, b)) # id 6

acmatch(hc, PACApp("+", (Var("x"), Var("y"))), pabc)
```

    [{'x': ACId(f='+', args=(0, 1)), 'y': 2},
     {'x': ACId(f='+', args=(0, 2)), 'y': 1},
     {'x': 0, 'y': ACId(f='+', args=(1, 2))},
     {'x': ACId(f='+', args=(1, 2)), 'y': 0},
     {'x': 1, 'y': ACId(f='+', args=(0, 2))},
     {'x': 2, 'y': ACId(f='+', args=(0, 1))}]

```python
acmatch(hc, PACApp("+", (Var("x"), PACApp("+", (Var("z"), Var("y"))))), pabc)
```

    [{'x': 0, 'z': 1, 'y': 2},
     {'x': 0, 'z': 2, 'y': 1},
     {'x': 1, 'z': 0, 'y': 2},
     {'x': 1, 'z': 2, 'y': 0},
     {'x': 2, 'z': 0, 'y': 1},
     {'x': 2, 'z': 1, 'y': 0}]

```python
acmatch(hc, PACApp("+", (Var("x"), PACApp("+", (Var("x"), Var("y"))))), pabc)
```

    []

```python
acmatch(hc, PACApp("+", (Var("x"), PACApp("+", (Var("x"), Var("y"))))), paab)
```

    [{'x': 0, 'y': 1}, {'x': 0, 'y': 1}]

```python
acmatch(hc, PACApp("+", (PApp("a", ()), PACApp("+", (PApp("b", ()), Var("y"))))), pabc)
```

    [{'y': 2}]

```python
acmatch(hc,PApp("f", (Var("x"),)), ffa)
```

    [{'x': 4}]

# Bits and Bobbles

AC congruence closure and AC ground completion are pre-existing things. AC term orderings are a thing (ACRPO and ACKBO). A nice thing about e-graphs compared to this is that it doesn't require so many complex conceptual priors

AC terms are conceptually quite simple to normalize. You flatten and sort. This can be thought of as a special kind of node that stores a multiset of its children rather than a vector.

AC matching is more challenging than simple syntactic matching, but not bad conceptually.

We only generate matches where a single application of the AC symbol is the identity and there is no 0-arity application. It may be reasonable to consider also allowing identity elements (0 for + or 1 for *) into the match. This should't change that much. Set-like matching also shouldn't be that different.

Take microegg, replace AC with just a hash cons
<https://www.philipzucker.com/weighted_uf/> do this with lpo? just store nxn lpo results?
Well, depth can short circuit it a little and max symbol
There is also ACKBO

The +{x} singleton kind of has an idempotence thing to it.
Pattern matching on that would branch on stripping it or not.

You can also do bottom up AC matching.

It'd be better to return the first bin and a generator of the remaining bins for early pruning. Whatever

1. Unique pointers
2. Reference counted pointers
3. Interned Ids
4. Multiple layers of referenced Ids (scoped hash consing). Perhaps a global and ephemeral arena.

You may want to intermix the representations. Hash conses can serve at least the following purposes:

1. Make structural and physical/pointer equality the same thing. Make equality checks faster.
2. Make a term bank you can search for stuff in
3. Reduce duplication for reduced memory usage

You don't need everything to be perfectly hash consed. You can do structural checks until you reach a point where you know perfect deduplication has been achieved.

For this reason it seems useful to have a notion of `ACId` sometimes in addition to a regular `Id`

```python
import itertools
def partitions(s, n):
    for assign in itertools.product(range(n), repeat=len(s)):
        bins = [[] for _ in range(n)]
        for x,b in zip(s, assign):
            bins[b].append(x)
        # possibly filter on nonempty or singleton or do map into ACId here
        yield tuple(tuple(bin) for bin in bins)

list(partitions("abc", 2))
```

    [(('a', 'b', 'c'), ()),
     (('a', 'b'), ('c',)),
     (('a', 'c'), ('b',)),
     (('a',), ('b', 'c')),
     (('b', 'c'), ('a',)),
     (('b',), ('a', 'c')),
     (('c',), ('a', 'b')),
     ((), ('a', 'b', 'c'))]

Inspired by Max's nice version of ematching, here is an AC matcher in a similar form

```python

```

I'm a little shaky about the length 0 and length 1 children case for ACNodes. It is not clear to me if they should be allowed or not.

```python
from dataclasses import dataclass,field
import itertools
type Id = int

@dataclass(frozen=True)
class ACId:
    f : str
    args : tuple[Id, ...]

type SId = Id | ACId # structured Ids. ACApp may be uninterned / ephemeral
# obviously it hurts to keep making copies of the same struct, but they are noticeably different

@dataclass(frozen=True)
class App:
    f : str
    args : tuple[Id, ...]

@dataclass(frozen=True)
class ACApp:
    f : str
    args : tuple[Id, ...]
type Node = App | ACApp

@dataclass(frozen=True)
class Var:
    name : str

@dataclass(frozen=True)
class PApp:
    f : str
    args : tuple['Pattern', ...]

@dataclass(frozen=True)
class PACApp:
    f : str
    args : tuple['Pattern', ...]

type Pattern = Var | PApp | PACApp

@dataclass
class ACHashCons:
    memo : dict[Node, Id] = field(default_factory=dict) # IndexMap
    nodes : dict[Id, Node] = field(default_factory=dict)

    def mk_node(self, node : Node) -> Id:
        if node in self.memo:
            return self.memo[node]
        else:
            id = len(self.nodes)
            self.nodes[id] = node
            self.memo[node] = id
            return id

    def mk_app(self, f : str, args : tuple[SId, ...]) -> Id:
        args = tuple(self._mk_acapp(arg.f, arg.args) if isinstance(arg, ACId) else arg for arg in args)
        return self.mk_node(App(f, args))

    # maybe you should never make an ac_app directory, only mk_app should call it? Is this overcomplicating it?
    #def mk_acapp(self, f : str, args : tuple[SId, ...]) -> SId:
        #args = tuple(args if isinstance(arg, int) else self._mk_acapp(arg.f, arg.args) for arg in args)
        # should also flatten
        # Should it flatten by searching into nodes too? No i think
        #flatargs = []
    #    return ACId(f, args)

    def mk_acapp(self, f : str, args : tuple[Id, ...]) -> Id:
        flatargs = [] 
        for id in args:
            assert isinstance(id, int)
            n = self.nodes[id]
            if isinstance(n, ACApp) and n.f == f:
                flatargs.extend(n.args)
            else:
                flatargs.append(id)
        flatargs.sort()
        return self.mk_node(ACApp(f, tuple(flatargs)))

    def acmatch_rec(self, p : Pattern, id : SId, subst) -> list[dict[str, Id]]:
        if isinstance(id, ACId):
            n = id
        else:
            n = self.nodes[id]
            if isinstance(n, ACApp):
                n = ACId(n.f, n.args) # could move this below Var for efficiency, but whatev
        match p, n:
            case Var(x), _:
                if x in subst:
                    if subst[x] == id:
                        return [subst]
                    else:
                        return []
                else:
                    newsubst = subst.copy()
                    newsubst[x] = id
                    return [newsubst]
            case PApp(pf, pargs), App(f, args) if pf == f and len(pargs) == len(args):
                substs = [subst]
                for parg, arg in zip(pargs, args):
                    substs = [subst for subst0 in substs for subst in self.acmatch_rec(parg, arg, subst0)]
                return substs
            case PACApp(pf, pargs), ACId(f, args) if pf == f:
                # we need to hand down temporary ACNodes
                # What about ACNode with 1 element? ACI easier?
                res = []
                for subargs in partitions(args, len(pargs)):
                    subargs = map(lambda a: ACId(f, a), subargs)
                    substs = [subst]
                    for parg, arg in zip(pargs, subargs):
                        substs = [subst for subst0 in substs for subst in self.acmatch_rec(parg, arg, subst0)]
                    res.extend(substs)
                return res
            case _:
                return []

        
    def acmatch(self, p : Pattern, id : Id) -> list[dict[str, Id]]:
        # flatten pattern?
        return self.acmatch_rec(p, id, {})

#for partition in itertools.combinations(args, len(pargs)): # wrong
#    for subargs in itertools.permutations(partition

hc = ACHashCons()
a = hc.mk_app("a", ())
b = hc.mk_app("b", ())
c = hc.mk_app("c", ())
pabc = hc.mk_acapp("+", (a, b, c))
fa  = hc.mk_app("f", (a,))
ffa = hc.mk_app("f", (fa,))

hc.acmatch(PACApp("+", (Var("x"), Var("y"))), pabc)
hc.acmatch(PACApp("+", (Var("x"), PACApp("+", (Var("z"), Var("y"))))), pabc)
hc.acmatch(PACApp("+", (Var("x"), PACApp("+", (Var("x"), Var("y"))))), pabc)
hc.acmatch(PApp("f", (Var("x"),)), ffa)

```

    [{'x': 4}]

Post hoc equalities may add new flattenings, so rebuilding involve AC flattening to make sure all AC flat forms exists.
Rebuilding becomes way more expensive
The Aegraph style of eagerly applying rewrites may avoid needing as much rebuilding though.

Rudi points out, what about right associated sorted regular hash consing. What about KBO on that?

Multisets of multiset rewriting. Take the  <https://www.philipzucker.com/multiset_rw/>
Nested multisets
Non well founded multisets? The AC to the ACI of non well founded sets

<https://pdfs.semanticscholar.org/08a6/9eb42f087ce76876aef224d32f2109367307.pdf> modular mutliset rewriting

# ACKBO

<http://cl-informatik.uibk.ac.at/software/ackbo/>
<https://arxiv.org/abs/1403.0406>

Ok the simplest ordering they describe puts all AC simple low, so they want to get pushed to leaved

# ACRPO

I still want to implement acrpo.

<https://research.vu.nl/ws/portalfiles/portal/266879340/A_Lambda_Free_Higher_Order_Recursive_Path_Order.pdf> implement lfrpo

Ground nominal term orderings.

Equivariance means that X = Y can't be oriented. or add(X,Y) = add(Y,X)
But we're ground so we're probably better behaved

Rudi noted that slots are lot of like unification vars that never get narrowed and have a disjointness constraint.
<https://egraphs.zulipchat.com/#narrow/channel/328972-general/topic/EGRAPHS.20Meeting.202025-03-20.3A.20Slotted.20E-Graphs/near/543056830>

If `t =g= s` was useful, what about `t <g< s`. Hmm. Ordered modulo g. Then we could talk about x + y < y + x ?

`2 <(-7)< -4` using shift group. Yes...  also `2 <-8< -4` but not `2 <-6< -4`
Combininig the inequality union find with the group union find.

An ordered group? <https://en.wikipedia.org/wiki/Linearly_ordered_group>
<https://ncatlab.org/nlab/show/ordered+group>
<https://en.wikipedia.org/wiki/Partially_ordered_group>

`def perm_lpo(t, s) -> tuple[Order, G]:`

<https://memoryleak47.github.io/slotted-egraphs-demystified-i/>
<https://medium.com/@mineralsteins/ultimate-code-compression-with-slotted-egraph-74f1859c9df5>

So we need an unfailing variant of knuth bendix

renamings aren't bijective. They are 1-1.

<https://www.cs.ru.nl/~cynthiakop/2024_isr/day2handout.pdf>  Termination:
the higher-order recursive path ordering - Kop

Have I done dumb ground kb in python?

<https://drops.dagstuhl.de/storage/00lipics/lipics-vol021-rta2013/LIPIcs.RTA.2013.319/LIPIcs.RTA.2013.319.pdf> normalized completion revisited. 2013. Has a table of moidifed rules. hmm. acrpo better than ackbo?

<https://www.jonmsterling.com/01JQ/> disentangling unfication and implciti coercions
"nested pattern unification" <https://andraskovacs.github.io/pdfs/wits23prez.pdf>

```python
class ACEGraph()
    def add_ac(self, f, args):
        flatargs = [[]]
        for id in args:
            this_arg = [[id]]
            for node in self.class[id]:
                match node:
                    case AC(f1, args1) if f1 == f:
                        this_arg.append(args1)
                    case _:
                        pass
            # expand out all ways of flattening
            flatargs = [prev + this for prev in flatargs for this in this_arg]
        children = []
        for args in flatargs: # maybe dedup first. Or whatever. add_prim will do that
            seld.add_prim(AC(f, sorted(args)))

        if AC(f, sorted(args)) in memo:
            return memo
        else:
            # do eager flattening
            # add in all E equivalent flattened terms
            for sub in powerset(args)
                if AC(f, sub) in memo:
                    id = mem(AC(f, sub))
                    AC
    def rebuild():
        add in flattenings
        
    def ematch(pattern, id)::
        for node in eclasses[id]:
            match node:
                case App
                case ACApp:
                    for all partitions:
                        match
```

      Cell In[14], line 1
        class ACEGraph()
                        ^
    SyntaxError: expected ':'

# A simple Manual Ground KB System

```python
from dataclasses import dataclass
@dataclass(frozen=True)
class App():
    f : str
    args : tuple["Term", ...] = ()

    def __len__(self) -> int:
        return 1 + sum(len(arg) for arg in self.args)

    def __repr__(self) -> str:
        if self.args:
            return f"{self.f}({', '.join(repr(arg) for arg in self.args)})"
        else:
            return self.f

    def __le__(self, other: "App") -> bool:
        return self == other or self < other
    def __lt__(self, other: "App") -> bool:
        if self == other:
            return False
        ls,lo = len(self), len(other)
        if ls != lo:
            return ls < lo
        if self.f != other.f:
            return self.f < other.f
        for sa, oa in zip(self.args, other.args):
            if sa != oa:
                return sa < oa
        return False
    def subst(self, a, b):
        if self == a:
            return b
        return App(self.f, tuple(arg.subst(a,b) for arg in self.args))    

x = App("x")
y = App("y")
f = lambda a,b: App("f", (a,b))
assert f(x,y) > x
assert y > x
assert not x > y
assert not x < x

@dataclass
class KB():
    E : list[tuple[App,App]]
    R : list[tuple[App,App]]
    # Ordering

    def orient(self, n: int):
        (a,b) = self.E.pop(n)
        assert b != a
        if b > a:
            a,b = b,a
        self.R.append((a,b))
        return self
    
    def triv(self, n : int):
        (a,b) = self.E.pop(n)
        assert a == b
        return self
    
    def simp(self, en : int, rn : int):
        (ae,be) = self.E.pop(en)
        (ar,br) = self.R[rn]
        self.E.append((ae.subst(ar,br), be.subst(ar,br)))
        return self
    
    def deduce(self, u : App, rleft : int, rright: int):
        (arl,brl) = self.R[rleft]
        (arr,brr) = self.R[rright]
        self.E.append((u.subst(arl,brl),
                       u.subst(arr,brr)))
        return self
    
    def rsimp(self, rn : int, rm : int):
        (ar,br) = self.R[rn]
        (am,bm) = self.R.pop(rm)
        self.R.append((am, bm.subst(ar,br)))
        return self

    def lsimp(self, rn : int):
        # TODO: need to dignify with encompassment condition
        self.E.append(self.R.pop(rn))
        return self



kb = KB([(f(x,y), y), (f(x,y), x)], [])

kb
kb.orient(0)
kb.simp(0,0)
kb
kb.orient(0)
kb.rsimp(1,0)
kb.deduce(f(x,y), 0, 1)
kb.orient(0)
kb.lsimp(1)
kb.simp(0,0)
kb.simp(0,1)
kb.triv(0)
```

    KB(E=[], R=[(y, x), (f(x, x), x)])

```python
# ok but it hsould be schedules
```

```python
from dataclasses import dataclass, field

counter = 0
def fresh_counter() -> int:
    global counter
    counter += 1
    return counter

@dataclass(frozen=True)
class Slot():
    name : int = field(default_factory=fresh_counter)

@dataclass(frozen=True)
class App():
    f : str
    args : tuple["Term", ...] = ()

type Term = App | Slot

```
