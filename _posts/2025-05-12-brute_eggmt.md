---
title: Brute Force E-Graphs Modulo Theories via SMT
date : 2025-05-12
---

E-graphs are a data structure for equational reasoning and optimization over ground terms. One of the benefits of e-graph rewriting is that it can declaratively handle useful but difficult to orient identities like associativity and commutativity (AC) in a generic way. However, using these generic mechanisms is more computationally expensive than using bespoke routines on terms containing sets, multi-sets, linear expressions, polynomials, and binders. A natural question arises: How can one combine the generic capabilities of e-graph rewriting with these specialized theories.

I wrote up a summary <https://arxiv.org/abs/2504.14340> of the last year or so ideas about E-Graph modulo theories.

While I was doing so, of course I was revisiting and comparing the different approaches and remembered a thread I hadn't pulled on

I have been playing with using Z3 and external e-graphs in various ways. Z3(py) is a super nice stable base to work off of so that I don't have to reimplement an AST and hash consing every time. It also leaves the possibility of using SMT solving, which can be really nice black box glue to tie things together.

- <https://www.philipzucker.com/z3_eq_sat/>  Egg-style Equality Saturation using only Z3. This uses z3 SimpleSolver to actually contain the e-graph.
- <https://www.philipzucker.com/ext_z3_egraph/> An External Z3 Egraph for Egraphs Modulo Theories. This makes a union find at the python layer.
- <https://www.philipzucker.com/egglog_z3_simp/> Conditional Simplification of Z3py Expressions with Egglog. This translates the z3 term into egglog, rewrites and turns it back

In the second post, as an after thought at the very very end I mention using Z3 itself to implement the equality check for e-matching. I guess I was more focussed on the ground rewrite system idea at the time and using z3 as guards which confused the exposition.

As I was writing this up, I also had a tickling in my head of this example <https://microsoft.github.io/z3guide/programming/Example%20Programs/Formula%20Simplification#subterm-simplification> from the z3 docs. What this is doing is scanning subterms for equivalent terms and replacing the big ones with the smaller ones. Here is the example pulled out:

```python
from z3 import *

def subterms(t):
    seen = {}
    def subterms_rec(t):
        if is_app(t):
            for ch in t.children():
                if ch in seen:
                    continue
                seen[ch] = True
                yield ch
                yield from subterms_rec(ch)
    return { s for s in subterms_rec(t) }

def are_equal(s, t1, t2):
    s.push()
    s.add(t1 != t2)
    r = s.check()
    s.pop()
    return r == unsat

def simplify(slv, mdl, t):
    subs = subterms(t)
    values = { s : mdl.eval(s) for s in subs }
    values[t] = mdl.eval(t)
    def simplify_rec(t):        
        subs = subterms(t)
        for s in subs:
            if s.sort().eq(t.sort()) and values[s].eq(values[t]) and are_equal(slv, s, t):
                return simplify_rec(s)
        chs = [simplify_rec(ch) for ch in t.children()]
        return t.decl()(chs)
    return simplify_rec(t)

H = Int('H')
s = Solver()
t = 4 + 4 * (((H - 1) / 2) / 2)
s.add(H % 4 == 0)
s.check()
m = s.model()
print(t, "-->", simplify(s, m, t))
```

    4 + 4*(((H - 1)/2)/2) --> H

In this example, one scans a term bank consisting of the subterms of the term to be simplified. This does not have to be the term bank though. It could be anything.

The rebuilding step of the e-graph can be be implemented using basically this technique.

I claim an e-graph is well represented by a termbank T and a union find.

I've found it to be somewhat expensive to do Z3 term manipulations from python, so it is better to refer to the terms by their id. This also complies well with the common e-graph way of talking about things.

All equalities are mirrored into the solver object. Because of this, queries to the solver can be used to implement congruence closure during rebuilding, and also any built terms using bottom up ematching can be semantically determined to be in the egraph or not by an smt query.

Everything I'm about to do should also be keyed on Z3 sort, but it makes the code more confusing.

```python
from kdrag.all import *
from dataclasses import dataclass
import itertools
@dataclass
class EGraph():
    roots : set[int] # current roots
    terms: dict[int, smt.ExprRef]  # all terms seen
    uf: dict[int, int]  # union-find structure
    solver : smt.Solver
    def __init__(self):
        self.roots = set()
        self.terms = {}
        self.uf = {}
        self.solver = smt.Solver()
    def find(self, t : smt.ExprRef) -> smt.ExprRef:
        eid = t.get_id()
        while eid in self.uf: # invariant: root not in uf.
            eid = self.uf[eid] 
        return self.terms[eid]
    def union(self, t1 : smt.ExprRef, t2 : smt.ExprRef):
        t1, t2 = self.add_term(t1), self.add_term(t2)
        if t1.eq(t2):
            return False
        else:
            id1, id2 = t1.get_id(), t2.get_id()
            self.uf[id1] = id2
            self.roots.remove(id1)
            self.solver.add(t1 == t2)
            return True
    def add_term(self, term : smt.ExprRef) -> smt.ExprRef:
        eid = term.get_id()
        if eid not in self.terms:
            self.roots.add(eid)
            self.terms[eid] = term
            for arg in term.children():
                self.add_term(arg)
            return term
        else:
            return self.find(term)
    def rebuild(self):
        # semantic rebuilding. Z3 already has congruence closure, so we only need one loop.
        oldroots = list(self.roots)
        for n, eid1 in enumerate(oldroots):
            for eid2 in oldroots[:n]:
                # Could do this better. The loop shrinks as we go along.
                # could also prune with models
                t1,t2 = self.terms[eid1], self.terms[eid2]
                if not self.find(t1).eq(self.find(t2)):
                    self.solver.push()
                    self.solver.add(t1 != t2)
                    res = self.solver.check()
                    self.solver.pop()
                    if res == smt.unsat:
                        self.union(t1, t2) # don't need to solver.add but whatev
    def in_terms(self, t : smt.ExprRef):
        # semantically check if t is in termbank
        if t.get_id() in self.terms: # fast path
            return True
        # semantically distinct from all roots
        self.solver.push()
        self.solver.add(smt.And([t != self.terms[rid] for rid in self.roots]))
        res = self.solver.check()
        self.solver.pop()
        return res == smt.unsat
    def ematch(self, n : int, f):
        """bottom up ematch and rewrite. f should take n arguments and return a tuple of two terms (lhs, rhs)"""
        for vs in itertools.product(self.roots, repeat=n):
            vs = [self.terms[v] for v in vs]
            (lhs, rhs) = f(*vs)
            if self.in_terms(lhs):
                print("found", lhs, "in terms")
                self.union(lhs, rhs)
        
x,y,z = smt.Ints("x y z")
E = EGraph()
E.union(x,y)
assert E.find(x).eq(y)

E = EGraph()
E.add_term(x)
E.add_term(y)
E.solver.add(x == y)
E.rebuild()
assert E.find(x).eq(y)



```

The following equation would take a lot of usage of rewrite rules for associativity, commutativity, and constant folding if we used generic egraph mechanisms. Here it is trivial. On the flipside, we now are doing a bunch of smt queries inside of rebuild and ematch.

```python
E = EGraph()
t1 = x + y + z + 1
t2 = 1 + y - 2 + x + 2 + z
E.add_term(t1)
E.add_term(t2)
assert not E.find(t1).eq(t2)
E.rebuild()
assert E.find(t1).eq(t2)
```

I have it printing to show all the terms in the termbank found that match `1 + v` semantically.

```python
E.ematch(1, lambda v: (1 + v, 1 + v))
E.rebuild()
```

    found 1 + 1 + y - 2 + x in terms
    found 1 + 1 in terms
    found 1 + 1 + y - 2 in terms
    found 1 + y in terms
    found 1 + x + y in terms
    found 1 + x + y + z in terms

# Bits and Bobbles

I put this into knuckledragger and I'll update it as seems useful <https://github.com/philzook58/knuckledragger/blob/main/kdrag/solvers/egraph.py> .

I could put this into more of the aegraph style. One would retain a vector buffer of seen terms and scan it for semantic matches to rewrite rules.

I guess we could side car into regular egg and do a z3 compression step every once in a while.

Why doesn't egg prune e-matching on models? We often have some idea of what models/examples look like. Inputs variables should be random examples, constants should be constants

Further optimizations should include

- Using models to prune possibilities. If we keep a cached model, or vector of models, we only need to check if things are equal in the model are _forced_ to e equal (justified equal).
- caching things we know aren't in the egraph to avoid repetitive smt checks

One question I have (had?) is that in my preprint I describe something like a Shostak procedure for e-graphs modulo theories in that it requires you to have theory specific canonizers. What would be the more Nelson-Oppen style of just informing each other / propagation of inferred equalities?

This style is reminescent of Ruler <https://github.com/uwplse/ruler> , which also used models to prune for possible equalities to learn. Instead of learning rewrite rules, we're "learning" via SMT query the e-graph itself. Since the e-graph represents ground rewrite rules, this also jives.

This is also reminiscent of SAT-sweeping and Fraiging. SAT sweeping uses sat queries to try and compress together semantically equialvanet nodes in a circuit. It's more of a thing in hardware verification world. <https://si2.epfl.ch/demichel/publications/archive/2020/DAC_2020_testa_luca.pdf>

Could also make a sympy version of bottom up + canonize.

Use alpha invariance trick. This would let us do light lambdas?

push pop
copy
model vectors for pruning. Need dummy values for each decl so at least model know what to define?

```python
# https://jamesbornholt.com/papers/diospyros-asplos21.pdf
BV16 = smt.BitVecSort(16)
BV8 = smt.BitVecSort(8)

x,y,z = smt.BitVecs("x y z", 16)
vadd = smt.Function('vadd', BV16, BV16, BV16)
vsub = smt.Function('vsub', BV16, BV16, BV16)
vmul = smt.Function('vmul', BV16, BV16, BV16)
vneg = smt.Function('vneg', BV16, BV16)
vmac = smt.Function('vmac', BV16, BV16, BV16, BV16)

vadd(x,y) == smt.Concat(smt.Extract(15, 8, x) + smt.Extract(15, 8, y), 
                        smt.Extract(7, 0, x) + smt.Extract(7, 0, y))

vsub(x,y) == smt.Concat(smt.Extract(15, 8, x) - smt.Extract(15, 8, y), 
                        smt.Extract(7, 0, x) - smt.Extract(7, 0, y))
vmul(x,y) == smt.Concat(smt.Extract(15, 8, x) * smt.Extract(15, 8, y),
                        smt.Extract(7, 0, x) * smt.Extract(7, 0, y))
vneg(x) == smt.Concat(-smt.Extract(15, 8, x), -smt.Extract(7, 0, x))
vmac(x,y,z) == smt.Concat(smt.Extract(15, 8, x) * smt.Extract(15, 8, y) + smt.Extract(15, 8, z),
                        smt.Extract(7, 0, x) * smt.Extract(7, 0, y) + smt.Extract(7, 0, z))

smt.prove(smt.Concat(smt.Extract(15, 8, x), smt.Extract(7, 0, x)) == x)

vadd(vmul(x,y),z) == vmac(x,y,z)


```

    proved

```python
s = smt.Solver()
s.check()
s.model().eval(x) # I don't hate that
```

x

```python
class UF():
    roots : set[int] # current roots
    #terms: dict[int, smt.ExprRef]  # all terms seen
    uf: dict[int, int]  # union-find structure

class EGraph():
    solver : smt.Solver
    univ : dict[int, smt.ExprRef]
    sorts : dict[smt.SortRef, UF]
```

```python
from kdrag.all import *
from dataclasses import dataclass
from collections import defaultdict

@dataclass
class EGraph():
    roots : defaultdict[smt.SortRef, set[int]]
    terms: defaultdict[smt.SortRef, dict[int, smt.ExprRef]] # tuple[int, smt.SortRef]?
    uf: defaultdict[smt.SortRef, dict[int, int]]
    solver : smt.Solver
    model : smt.ModelRef
    modelvals : defaultdict[smt.SortRef, dict[int, list[int]]] # map from sort to id of value in model to list of roots with that value in model.
    def __init__(self):
        self.roots = defaultdict(set)
        self.terms = defaultdict(dict)
        self.uf = defaultdict(dict)
        self.solver = smt.Solver()
        self.solver.check()
        self.model = self.solver.model()
        self.modelvals = defaultdict(dict)
    def _find_id(self, s : smt.SortRef, eid : int) -> int:
        uf = self.uf[s]
        while eid in uf:
            eid = uf[eid]
        return eid
    def find(self, t : smt.ExprRef) -> smt.ExprRef:
        s = t.sort()
        return self.terms[s].get(self._find_id(s, t.get_id()), t)
    def _raw_union(self, s : smt.SortRef, eid1 : smt.ExprRef, eid2 : smt.ExprRef):
        id1, id2 = self._find_id(s, eid1), self._find_id(s, eid2)
        if id1 == id2:
            return id2
        else:
            self.uf[s][id1] = id2
            self.roots[s].discard(id1)
            return id2
    def union(self, t1 : smt.ExprRef, t2 : smt.ExprRef):
        id1, id2 = self.add_term(t1), self.add_term(t2) # should we add terms?
        if id1 == id2:
            return id2
        else:
            s = t1.sort()
            # Could check if constructor or other value and let win.
            # tie break towards things in terms. Then we could allow things not in terms to be in uf.
            self.uf[s][id1] = id2
            self.solver.add(t1 == t2)
            self.roots[s].discard(id1)
            return id2  
    def add_term(self, term : smt.ExprRef):
        eid = term.get_id()
        s = term.sort()
        if eid not in self.terms[s]:
            self.roots[s].add(eid)
            self.terms[s][eid] = term
            for arg in term.children():
                self.add_term(arg)
            return eid
        else:
            return self._find_id(s, eid)
    def in_terms(self, term : smt.ExprRef, strong=True) -> bool:
        s = term.sort()
        #self.solver.add(smt.Not(smt.Distinct(term, self.terms[s][term.get_id()])))
        roots = self.roots[s]
        if self._find_id(s, term.get_id()) in roots: # why am I not looking in terms?
            return True 
        elif strong:
            # should prune based on model.
            self.solver.push()
            for eid in self.roots[s]:
                term2 = self.terms[s][eid]
                self.solver.add(term2 != term) # could do as single 
                res = self.solver.check()
                if res == smt.unsat:
                    self.solver.pop()
                    self._raw_union(s, term.get_id(), eid) # interesting. Don't put into term bank, but do cache union for later.
                    return True
            self.solver.pop()
            return False
        else:
            return False
    def rebuild(self):
        for s, roots in self.roots.items(): 
            # faster single distinct check?
            oldroots = list(roots)
            for n, eid1 in enumerate(oldroots):
                for eid2 in oldroots[:n]:
                    # Could do this better. The needed loop shrinks as we go along.
                    if self._find_id(s, eid1) != self._find_id(s, eid2):
                        self.solver.push()
                        terms = self.terms[s]
                        t1,t2 = terms[eid1], terms[eid2]
                        self.solver.add(t1 != t2)
                        res = self.solver.check()
                        if res == smt.unsat:
                            self._raw_union(s, eid1, eid2) # don't need to solver.add
                        self.solver.pop()
        assert self.solver.check() == smt.sat
        for s, roots in self.roots.items():
            for eid in roots:
                if eid not in self.terms[s]:
                    self.roots[s].discard(eid)
        self.model = self.solver.model()
    def extract(self, term : smt.ExprRef) -> smt.ExprRef: ...

x,y,z = smt.Ints("x y z")
E = EGraph()
E.union(x,y)
assert E.find(x).eq(y)

E = EGraph()
E.add_term(x)
E.add_term(y)
E.solver.add(x == y)
E.rebuild()
assert E.find(x).eq(y)

E = EGraph()
E.add_term(x)
E.solver.add(x == y)
print(E.find(y))
E.in_terms(y)
E.find(y)
# strong_find = rebuild + find

# in_terms does a mini rebuild kind of.
# May want to cache what _isn't_ in terms also... Hmm.
```

    y

x

```python

from kdrag.all import *
from dataclasses import dataclass
import itertools
@dataclass
class EGraph():
    roots : set[int] # current roots
    terms: dict[int, smt.ExprRef]  # all terms seen
    uf: dict[int, int]  # union-find structure
    solver : smt.Solver
    def __init__(self):
        self.roots = set()
        self.terms = {}
        self.uf = {}
        self.solver = smt.Solver()
    def find_id(self, eid : int) -> int:
        # union find lookup
        while eid in self.uf:
            eid = self.uf[eid]
        return eid
    def find(self, t : smt.ExprRef) -> smt.ExprRef:
        return self.terms[self.find_id(t.get_id())]
    def raw_union(self, eid1 : smt.ExprRef, eid2 : smt.ExprRef):
        # union without reflection into solver
        id1, id2 = self.find_id(eid1), self.find_id(eid2)
        if id1 == id2:
            return False
        else:
            self.uf[id1] = id2
            self.roots.remove(id1)
            return True
    def union(self, t1 : smt.ExprRef, t2 : smt.ExprRef):
        # union with refelction into solver
        id1, id2 = self.add_term(t1), self.add_term(t2)
        if self.raw_union(id1, id2):
            self.solver.add(t1 == t2)
            return True
        else:
            return False
    def add_term(self, term : smt.ExprRef):
        eid = term.get_id()
        if eid not in self.terms:
            self.roots.add(eid)
            self.terms[eid] = term
            for arg in term.children():
                self.add_term(arg)
            return eid
        else:
            return self.find_id(eid)
    def rebuild(self):
        oldroots = list(self.roots)
        for n, eid1 in enumerate(oldroots):
            for eid2 in oldroots[:n]:
                # Could do this better. The needed loop shrinks as we go along.
                if self.find_id(eid1) != self.find_id(eid2):
                    t1,t2 = self.terms[eid1], self.terms[eid2]
                    self.solver.push()
                    self.solver.add(t1 != t2)
                    res = self.solver.check()
                    self.solver.pop()
                    if res == smt.unsat:
                        self.raw_union(eid1, eid2) # don't need to solver.add
    def in_terms(self, t : smt.ExprRef):
        if t.get_id() in self.terms: # fast path
            return True
        # semantically distinct from all roots
        self.solver.push()
        self.solver.add(smt.And([t != self.terms[rid] for rid in self.roots]))
        res = self.solver.check()
        self.solver.pop()
        return res == smt.unsat
    def ematch(self, n : int, f):
        for vs in itertools.product(self.roots, repeat=n):
            vs = [self.terms[v] for v in vs]
            (lhs, rhs) = f(*vs)
            if self.in_terms(lhs):
                print("found", lhs, "in terms")
                self.union(lhs, rhs)
```

```python
from kdrag.all import *
from dataclasses import dataclass

@dataclass
class EGraph():
    roots : set[int]
    terms: dict[int, smt.ExprRef]
    explain : dict[int, object]
    uf: dict[int, int]
    solver : smt.Solver
    def __init__(self):
        self.roots = set()
        self.terms = {}
        self.uf = {}
        self.solver = smt.Solver()
    def find_id(self, eid : int) -> int:
        while eid in self.uf:
            eid = self.uf[eid]
        return eid
    def find(self, t : smt.ExprRef) -> smt.ExprRef:
        return self.terms[self.find_id(t.get_id())]
    def raw_union(self, eid1 : smt.ExprRef, eid2 : smt.ExprRef):
        id1, id2 = self.find_id(eid1), self.find_id(eid2)
        if id1 == id2:
            return id2
        else:
            self.uf[id1] = id2
            self.roots.remove(id1)
            return id2
    def union(self, t1 : smt.ExprRef, t2 : smt.ExprRef):
        id1, id2 = self.add_term(t1), self.add_term(t2)
        if id1 == id2:
            return id2
        else:
            self.uf[id1] = id2
            self.solver.add(t1 == t2)
            self.roots.remove(id1)
            return id2  
    def add_term(self, term : smt.ExprRef):
        eid = term.get_id()
        if eid not in self.terms:
            self.roots.add(eid)
            self.terms[eid] = term
            for arg in term.children():
                self.add_term(arg)
            return eid
        else:
            return self.find_id(eid)
    def rebuild(self):
        oldroots = list(self.roots)
        for n, eid1 in enumerate(oldroots):
            for eid2 in oldroots[:n]:
                # Could do this better. The needed loop shrinks as we go along.
                if self.find_id(eid1) != self.find_id(eid2):
                    self.solver.push()
                    t1,t2 = self.terms[eid1], self.terms[eid2]
                    self.solver.add(t1 != t2)
                    res = self.solver.check()
                    if res == smt.unsat:
                        self.raw_union(eid1, eid2) # don't need to solver.add
                    self.solver.pop()
```

keying on sort makes it more complex a little, but also prunes some possible comparisons (which are nonsenical anyway)

```python

```

```python
@dataclass
class EGraph():
    canon_terms : dict[int, smt.ExprRef]
    terms : dict[int, smt.ExprRef]
    uf : dict[int, int]
    solver : smt.Solver
    #models : list[m]
    #sigs : dict[tuple[Value,...], list[TermRef]]
    #explain :   #  dict[(int,int), unsat cores]

    def add_term(self, t):
        if t.get_id() not in self.terms:
            self.terms[t.get_id()] = t
            for c in t.children():
                self.add_term(c)
    def term_matches(self, t): # guard=None
        #self.solver.push()
        #self.solver.add(cond)
        # prune by models?
        for s in self.canon_terms.values():
            self.solver.push()
            self.solver.add(t != s)
            res = self.solver.check()
            self.solver.pop()
            if res == smt.unsat:
                yield s

    def union(self, e1, e2):
        self.solver.add(e1 == e2)
        # orient by smaller depth or sexpr size. Kind of could get some sharing action
        # maybe immediately remove e1 e2
        """
        e1 = self.find(e1)
        e2 = self.find(e2)
        if e1.eq(e2):
            return e1
        else:
            del self.canon_terms[e1.get_id()]
            self.terms[e1.get_id()] = e1
        """

    def rebuild(self):
        for t in self.canon_terms.values():
            for s in self.matches(t):
                self.union(t, s)
```

SMT as a theory. SMT solvers themselves present the interface of a theory.

Cody says _is_ interpolation.
If whole theory is unsat  A /\ B, there exists C that only has shared symbols such that A /\ C and B /\ C are unsat.

Nelson Oppen style combination of theories vs Shostak.
Nelson oppen theories

<https://web.stanford.edu/class/cs357/lecture11.pdf>

```python
class Theory():
    def register_term(self, term) -> V:
    def assert_eq(self, a, b) -> list[tuple[V,V]]: # propagates
    def is_eq(self, a, b) -> Option[bool]:  # True if justified true, false if can't be true, None if both possible.

    
```
