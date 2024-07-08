---
title: An External Z3 Egraph for Egraphs Modulo Theories
date: 2024-07-07
---

`EMT ~ SMT - SAT`

Satisfiability Modulo Theories is basically SAT + Egraph + bits of other things like linear programming. The egg paper ematching algorithm is based off the one described for z3. Even if it isn't intended for the use case, one feels like the z3 egraph and ematcher would be mighty convenient thing for equality saturation.

So it has a been a source of sadness for a long time that SMT solvers hold all sorts of bits and pieces that can't be easily abused off label.
[Z3](https://microsoft.github.io/z3guide/docs/logic/intro/) is super engineered and has bindings everywhere. It's a great platform, but I understand the project has it's own goals and desires that may not comply with whatever fancy I have for the next 15 seconds.

Well, I've been thinking about it, and there is a pretty tight little implementation of an external egraph made possible by the z3 ast functions exposed, in particular `substitute` which can replace ground terms by other grounds terms in an expression. We can use this to build a [Ground Rewrite System style egraph](https://www.philipzucker.com/egraph2024_talk_done/). Adding to this the technique of bottom up e-matching, we can search over our egraph and assert theory specific constraints into the system and use them as guards (for disequality constraints or linear inequality constraints). We can also reuse the built in z3-simplifier, which can be quite handy.

First we can make cached functions that tells us the size of a term and a function that returns terms in some term order. This is sort of a half-assed knuth bendix term order that tie breaks equal sized terms by the effectively random term id. I'm not so sure this cowboy term ordering is ok, so maybe implementing a real [ground knuth bendix ordering](https://www.philipzucker.com/ground_kbo/) is in order

```python
from z3 import *
from dataclasses import dataclass
from functools import cache
from itertools import product
from collections import defaultdict

@cache
def z3_size(e):
    if is_app(e):
        return 1 + sum(z3_size(a) for a in e.children())
    return 1

@cache
def is_value(x):
    return is_int_value(x) or is_rational_value(x) or is_algebraic_value(x) or is_bv_value(x) or is_finite_domain_value(x) or is_string_value(x) or is_fp_value(x) or is_K(x)

def order(t1,t2):
    s1,s2 = z3_size(t1), z3_size(t2)
    if s1 > s2:
        return (t1, t2)
    elif s2 > s1:
        return (t2, t1)
    # values should be preferred
    elif is_value(t1) and not is_value(t2):
        return (t2, t1)
    elif is_value(t2) and not is_value(t1):
        return (t1, t2)
    else:
        if t1.get_id() > t2.get_id(): # yeaaaa, I'm not sure this is ok.
            return (t1, t2)
        else:
            return (t2, t1)
```

Next the actual egraph itself, which I think is shockingly simple.

The egraph has a

- `E` set of equations `lhs = rhs`
- `R` set of rewrite rules `lhs -> rhs

These are the pieces of a knuth bendix completion system. See "Term Rewriting and All That" for more.

In addition, the egraph has

- `T` a set of search terms. Separating out `T` from `R` makes ematching into the egraph more straightforward. Conceptually, an egraph holds a possibly infinite class of terms. The class of terms is the set `T` rewritten backwards `rhs -> lhs` using rules from `R`. It so happens that it is most convenient to index T by sort, since when we ematch, we will only be looking for terms of particular sort.
- `solver` a z3 solver into which we will reflect any equality we discover, but also theory specific facts.

```python
@dataclass
class EGraph():
    R: list[tuple[ExprRef, ExprRef]] # rewrite rules
    E: list[tuple[ExprRef, ExprRef]] # equations
    T: dict[SortRef, set[ExprRef]] # set of terms of a given sort
    def __init__(self):
        self.solver = Solver()
        self.R = []
        self.E = []
        self.T = defaultdict(set) 
    def add_term(self, term):
        """ recursively add terms and its children into T"""
        self.T[term.sort()].add(term)
        for t in term.children():
            self.add_term(t)
    def reduce_term(self, e : z3.ExprRef, R=None):
        if R == None:
            R = self.R
        """ aka find. Fully reduce term with respect to R"""
        while True:
            e1 = z3.substitute(e, *R)
            if e.eq(e1): #fixpoint
                return e
            e = e1
    def extract(self, t: z3.ExprRef) -> z3.ExprRef:
        """ Same a reduce. See ground completion blog post"""
        return self.reduce_term(t)
    def union(self, t1 : ExprRef, t2: ExprRef):
        """Assert an equality between ground terms"""
        t1 = self.reduce_term(t1)
        t2 = self.reduce_term(t2)
        if not t1.eq(t2):
            self.solver.add(t1 == t2) # reflect equality into solver
            #self.E.append((t1, t2)) # no reason to assert into E really.
            t1,t2 = order(t1, t2)
            self.R.append((t1, t2))
    def canon(self):
        """Partially Recanonize the egraph. Rules R are interreduced, and T is reduced with respect to R. I'm not happy with this part"""
        R = set()
        while self.R:
            t1,t2 = self.R.pop()
            t1 = self.reduce_term(t1, R=list(R)+self.R)
            t2 = self.reduce_term(t2, R=list(R)+self.R)
            if not t1.eq(t2):
                t1, t2 = order(t1, t2)
                R.add((t1,t2))
        self.R = list(R)
        self.T = {k : set(self.reduce_term(t) for t in Ts) for k,Ts in self.T.items()}
    def guard(self, C : z3.BoolRef):
        """Using z3 to implement a provable guard."""
        self.solver.push()
        self.solver.add(Not(C))
        res = self.solver.check()
        self.solver.pop()
        if res == unsat:
            return True
        else:
            return False
    def rw(self, sorts : list[z3.SortRef], f, add_term=True): # guard keyword param?
        """ A rewrite rule with variables from the sorts list. 
            `f` is a function that takes the variables and returns a pair of terms.
            `add_term` is a flag to determine if we add the new term
        """
        for t in product(*[self.T[sort] for sort in sorts]):
            lhs, rhs = f(*t)
            lhs = self.reduce_term(lhs) 
            if lhs in self.T[lhs.sort()]:
                if add_term:
                    # if add is false, we never increase T. It will terminate. This is yihong's thing?
                    self.add_term(rhs)
                self.union(lhs, rhs)
    def z3_simplify(self):
        """ asserting built in z3 rules to the external egraph
            One of the perks of piggybacking on z3"""
        for tset in self.T.values():
            for t in tset:
                t1 = z3.simplify(t)
                if not t1.eq(t):
                    self.union(t, t1)
    def iter(self, *sorts):
        """Iterate over all possible terms of the given sorts. Can use this to implement rules/smarter rewrites."""
        return product(*[self.T[sort] for sort in sorts])
```

Kind of the cutest part is

```python
    def reduce_term(self, e : z3.ExprRef):
        """ aka find. Fully reduce term with respect to R"""
        while True:
            e1 = z3.substitute(e, *self.R)
            if e.eq(e1): #fixpoint
                return e # simplify(e) reuse built in z3 simplify?
            e = e1
```

Where we can use `substitute` to perform our ground rewriting for us.

Here is some usage.
We can see that after unioning some terms, the term set shrinks.

```python
x,y,z = Reals("x y z")
E = EGraph()
E.add_term(RealVal(1))
E.add_term(x + (y + z))
E.union(x, y)
E.union(x + x, z)
print("starting system", E)
E.canon()
print("smaller term set: ", E)
E.union(x,z)
E.canon()
print("even smaller term set: ", E)

```

    starting system EGraph(R=[(y, x), (x + x, z)], E=[], T=defaultdict(<class 'set'>, {Real: {y, z, x, 1, y + z, x + y + z}}))
    smaller term set:  EGraph(R=[(y, x), (x + x, z)], E=[], T={Real: {z, x, x + z, 1, x + x + z}})
    smaller term set:  EGraph(R=[(y, x), (z, x), (x + x, x)], E=[], T={Real: {x, 1}})

The way I encode the ematcher makes it seem like there is nothing there, and there kind of isn't. Bottom up ematching is extremely simple. You guess which term will end up in the variables. We can sort of shallowly embed rules in a "minikanren" like way (like the `fresh` combinator) with a lambda that takes in all the pattern variables and just builds the left hand and right hand side of the rules.
You could also use the `iter` function, which would let you write your rules in your own loops. This might be useful for early failing, parallelization, etc.

```python
x,y,z = Reals("x y z")
E = EGraph()
E.add_term(x + (y + z))
print(E)
E.rw([RealSort(), RealSort()], lambda x,y: (x + y, y + x))
print(E)
E.canon()
E
```

    EGraph(R=[], E=[], T=defaultdict(<class 'set'>, {Real: {y, z, x, y + z, x + y + z}}))
    EGraph(R=[(z + y, y + z), (y + z + x, x + y + z)], E=[], T=defaultdict(<class 'set'>, {Real: {y, z, x, z + y, y + z + x, y + z, x + y + z}}))





    EGraph(R=[(z + y, y + z), (y + z + x, x + y + z)], E=[], T={Real: {y, z, x, y + z, x + y + z}})

We can use z3 solver queries to implement guards. Guards don't bind new variables, but that doesn't seem like that much of an impediment since we already support multipatterns.

```python
print("Before positivity assertion:")
for (x,) in E.iter(RealSort()):
    if E.guard(x >= 0):
        print(x, "is non-negative")
        # could put guarded rewrite rule here.

E.solver.push()

for (x,) in E.iter(RealSort()):
    E.solver.add(x >= 0)

print("After positivity assertion:")
for (x,) in E.iter(RealSort()):
    if E.guard(x >= 0):
        print(x, "is non-negative")

E.solver.pop()
```

    Before positivity assertion:
    1 is non-negative
    After positivity assertion:
    z is non-negative
    x is non-negative
    x + z is non-negative
    1 is non-negative
    x + x + z is non-negative

In a limited way, we can use the built in z3 simplifier. This can get us constant folding for example. This is kind of ad hoc (even more so than some of the rest), but interesting. Maybe there is some other way to use the z3 simplifier in a more intrinsic way?

```python
    def z3_simplify(self):
        """ asserting built in z3 rules to the external egraph
            One of the perks of piggybacking on z3"""
        for tset in self.T.values():
            for t in tset:
                t1 = z3.simplify(t)
                if not t1.eq(t):
                    self.union(t, t1)
```

Something is behaving very badly here, which is concerning. Two terms which should hash cons to the same value are not.

```python
x,y,z = Reals("x y z")
E = EGraph()
E.add_term(RealVal(1))
E.add_term(x + (y + z))
E.union(x, RealVal(1))
E.union(y, RealVal(2))
E.z3_simplify()
print(E)
E.canon()
E.z3_simplify()
print(E)
E.canon()
print(E.extract(x + y + z))
E
E.canon()
e = E.extract(x + y + z)
e1 = E.extract(e)
print(e1)
E.canon()
E
# identicval but different, Z3 isn't perfect hash consing?
E.R[0][0].sexpr()
print(E.R[1][0].sexpr())
print(E.R[1][0].get_id())
print(E.R[0][0].get_id())
print(E)

```

    EGraph(R=[(x, 1), (y, 2), (1 + 2 + z, 1 + 2 + z)], E=[], T=defaultdict(<class 'set'>, {Real: {y, z, x, 1, y + z, x + y + z}}))
    EGraph(R=[(x, 1), (y, 2), (1 + 2 + z, 1 + 2 + z), (1 + 2 + z, 3 + z)], E=[], T={Real: {2, 1 + 2 + z, z, 1, 2 + z}})
    1 + 2 + z
    1 + 2 + z
    (+ 1.0 2.0 z)
    46
    45
    EGraph(R=[(1 + 2 + z, 3 + z), (1 + 2 + z, 3 + z), (y, 2), (x, 1)], E=[], T={Real: {2, 3 + z, z, 1, 2 + z}})

# Bits and Bobbles

`EMT ~ SMT - SAT` is slightly inaccurate because we want minimal models. Also we want the `simp : Term -> Term` mode rather than `prove_eq : Term -> Term -> Bool` mode

If you wanted to, you could do the same thing here with egg or egglog, by reflecting every equality learned into a solver object held by the egraph. This solver is then available for use in guards.

An alternative approach might be the have z3_formula be objects inside your egraph, an external datatype like f64 or string. This is somewhat like the formulog approach.

We can also support rules and multipatterns

```python
    def rule(self, n, f):
        """
         f produces a lhs => rhs thing that 
        """
        for t in product(self.T, repeat=n):
            lhs, rhs = f(*t)
            self.solver.push()
            self.solver.add(Not(And(lhs)))
            res = self.solver.check()
            self.solver.pop()
            if res == unsat:
                self.solver.add(And(rhs))
```

Z3 can also be used for subsumption checks to see if new info is redundant with respect to already derived data, or perhaps to back subsume already derived constraints. I figured for a first pass, just let z3 have it all. It probably has it's own more efficient subsumption mechanisms than me doing it manually

The newly exposed egraph innards. Only from C++ api? Undocumented, unsupported. <https://x.com/BjornerNikolaj/status/1764793235246076313>

Using z3 egraph via the official smtlib interface. It's tricky / impossible. More on that in future Justified SMT block posts.

Note for example this system, which you might hope returns `a = b = c = Val!0` `d = f = Val!1` does return a valid first order model where all constants collapse to the same value in the model. This is not the model with the minimal number of equalities though, so this is not what we want.

```python
from z3 import *
S = DeclareSort("S")
a,b,c,d,e,f = Consts("a b c d e f", S)

s = Solver()
s.add(a == b)
s.add(b == c)
s.add(d == f)
s.check()
s.model()
```

[f = S!val!0,
 d = S!val!0,
 c = S!val!0,
 a = S!val!0,
 b = S!val!0]

Note that however this two layered version does work. Quite curious. I don't think strictly speaking it _has_ to work though.

```python
from z3 import *
S = DeclareSort("S")
S1 = DeclareSort("S1")
a,b,c,d,e,f = Consts("a b c d e f", S)
i = Function("i", S, S)

s = Solver()
s.add(Distinct(a,b,c,d,e,f))
s.add(i(a) == i(b))
s.add(i(b) == i(c))
s.add(i(d) == i(f))
s.check()
s.model()
```

[d = S!val!3,
 f = S!val!5,
 e = S!val!4,
 b = S!val!1,
 a = S!val!0,
 c = S!val!2,
 i = [S!val!3 &rarr; S!val!7, S!val!5 &rarr; S!val!7, else &rarr; S!val!6]]

# Another approach

Interesting idea, instead of using the reduction via `R` to do s subsumption check in `union` or to ematch into `T` we can cast both as smt queries themselves.

Quite brute force, quite a lot of z3 calls.
Something like this.

```python

from dataclasses import dataclass
from z3 import *
@dataclass
class EGraph():
    E: list[tuple(ExprRef, ExprRef)]
    T: dict[SortRef]
    def __init__(self):
        self.E = []
        self.T = defaultdict(set)
        self.solver = Solver()
    def add_term(self, t):
        self.T[t.sort()].add(t)
        if is_app(t):
            for t in t.children():
                self.add_term(t)
    def union(self, t1, t2, reason=None):
        # use solver for subsumption check rather than reducing.
        self.solver.push()
        self.solver.add(t1 != t2)
        res = self.solver.check()
        self.solver.pop()
        if res == sat: # non redundant info
            self.solver.assert_and_track(t1 == t2, ) # add and track?
            self.E.append((t1,t2, reason)) # add reason
    def rw(self, sorts, f):
        for xs in product(*[self.T[sort] for sort in sort]): # maybe I could internalize this loop into z3 too?
            lhs, rhs = f(xs)
            self.solver.push()
            # this avoids the reduction step to check if in self.T
            self.solver.add(Not(Or(lhs == t for t in self.T[lhs.sort()]))
            res = self.solver.check() # can give unsat core reason for why lhs == pat[xs]. Is this actually  useful?
            self.solver.pop()
            if res == unsat:
                core = self.get_unsat_core()

                self.union(lhs, rhs, reason=("rule", core))
```
