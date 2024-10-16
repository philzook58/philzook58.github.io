---
title: "Towards an AC Egraph : Grobner, Graver Bases and Ground Multiset Rewriting"
date: 2024-10-16
---

[Egraph](https://egraphs.org/) rewriting is a methodology for optimizing expression. A known problem is that some of the rewrite rules explode the egraph in size for what feels like common administrative manipulations like `a + b = b + a` or `a * (b * c) = (a * b) * c`.

In this blog post <https://www.philipzucker.com/linear_grobner_egraph/> I described a methodology for extending the egraph by replacing the union find with more theory specific equational solvers. From this perspective, the union find (ground atomic equations) is in a spectrum of theories for which knuth bendix completion is guaranteed to terminate. When we have a class of equations that are guaranteed to be completable, it means we can throw together discovered application specific equations and get a normalizing rewrite system out.

The union find is a normalizer for ground atomic equations like `a = b, b = c`, whereas row echelon from and groebner bases are normalizers for linear and polynomials equations. Once we have a normalizer, we can canonize our "eclass ids". When we "union" we insert a new application specific equation into the theory solver.

An interesting common theme that I think is developing is that of "structured eids". This is the place we can place theory specific equational solvers. Other examples that have this feel are the extra structure in slotted egraphs, which carry the bound variable slots in the eid or colored egraphs where eids carry a context. In hindsight, egg 1.0 style analyses can be seen as a kind of a lattice "structured eid" consisting of a tuple of regular eid and lattice value. Another structured eid example is the "group" union find that can tag union find edges with a group action <https://www.philipzucker.com/union-find-groupoid/> .

String knuth bendix <https://www.philipzucker.com/string_knuth/> is what you might use if you want an intrinsic bolted in notion of concatenation, a "sequence egraph". In other words, wee can label some operators as intrinsically associative. String knuth bendix is not guaranteed to terminate and is less well behaved than Grobner basis production. In this case the "structured eids" are strings/lists/vectors/sequences of eids.

A common request is for associative and commutative theory. I a little bit suspect people want this for operators that are actually commutative ring-like, for which groebner basis are more appropriate. Nevertheless, there _is_ a thing that is guaranteed to complete the equations for AC theories.

You can view this AC solving thing from different angles.

- Grobner bases for toric/binomial systems like `x y^2 z - x = 0`. Under buchberger's algorithm, this binomial structure is maintained. You can write this as `x y^2 z = x`. The "AC-ness" is coming from that multiplication is associative and commutative in commutative algebra. Each monomial is a multiset of the variables.
- Hilbert bases - hilbert bases are generating set of cone (positive combination of vector) restricted to lattice (integer) points. <https://en.wikipedia.org/wiki/Hilbert_basis_(linear_programming)>
- Graver bases - <https://en.wikipedia.org/wiki/Graver_basis> are a finite basis of the integer points of `Ax=0` such that any vector can be written as a linear positive integer sum of them and they are minimal according to a well founded (terminating) order.
- Ground Multiset Completion

I think the last perspective is the most direct, but beauty is in the eye of the beholder.

It's also quite interesting that all of these can be used to solver integer linear programming problems. You can convert your problem into an appropriate basis and then you have a greedy fast no-search algorithm to solve it after that is done. The caveat is of course that finding this basis or completed rewrite system is very expensive. We'll show an example later

# Theories and Data Structures

If I take a binary expression `(x + y) + (z + x)`, there are different data structures that feel appropriate for the different axioms I might assume. I discuss this also here <https://www.philipzucker.com/hashing-modulo/>

If I have no axioms, I can use a tree. `(("x","y"),("z","x"))`

If I have C, I should sort these tuples. `(("x","y"),("x","z"))`

If I have A, I can drop parens. a List is appropriate `["x", "y", "z", "x"]

If I have AC, I should sort the list `["x", "x", "y", "z"]` or equivalently collect up the multiple counts `[("x", 2), ("y", 1), ("z", 1)]`. This is a multiset data structure. Maybe you want to use a dictionary `{"x": 2, "y": 1, "z": 1}`. Same diff.

If I have ACI, I should sort and dedup the list `["x", "y", "z"]`. This is a set data structure. Maybe you want to use some more clever set data structure. Same diff.

# Ground Multiset Completion

Ok, so we want to bolt AC into the egraph. I claim then that a good notion of "eid" is a multiset. The way we normalize these "eids" is by rewriting them using a completed ground multiset system, the appropriate generalization of the union find for this case.

The way we do this is we follow exactly the same generic lines as all completion procedures.

First we define a notion of overlap of multisets. This generates critical pairs where confluence might fail. Overlap for multisets is the least multiset which contains both.

I'm using the sorted list representation of multisets. It's easy enough to do this in a sort of sorted merge like fashion, as you muight see in mergesort

<https://en.wikipedia.org/wiki/Merge_algorithm>

```python
def overlap(xs, ys):
    """Find minimal multiset that is a supermultiset of both xs and ys. Return None if this is just the union (trivial)"""
    nontriv = False
    res = []
    i,j = 0,0
    while i < len(xs) and j < len(ys):
        x,n = xs[i]
        y,m = ys[j]
        if x < y:
            res.append((x, n))
            i += 1
        elif x > y:
            res.append((y, m))
            j += 1
        else:
            nontriv = True
            res.append((x, max(n,m)))
            i += 1
            j += 1
    if not nontriv:
        return None
    while i < len(xs):
        res.append(xs[i])
        i += 1
    while j < len(ys):
        res.append(ys[j])
        j += 1
    return res

assert list(overlap([("a", 1), ("b", 2)], [("a", 1), ("c", 3)])) == [("a", 1), ("b", 2), ("c", 3)]
assert overlap([("a", 1), ("b", 2)], [("c", 1)]) is None
```

It's also nice to have a notion of multiset difference and sum. <https://en.wikipedia.org/wiki/Multiset>

```python


def add(xs,ys):
    """add two multisets"""
    res = []
    i,j = 0,0
    while i < len(xs) and j < len(ys):
        x,n = xs[i]
        y,m = ys[j]
        if x < y:
            res.append((x, n))
            i += 1
        elif x > y:
            res.append((y, m))
            j += 1
        else:
            res.append((x, n+m))
            i += 1
            j += 1
    while i < len(xs):
        assert j == len(ys)
        res.append((xs[i]))
        i += 1
    while j < len(ys):
        assert i == len(xs)
        res.append((ys[j]))
        j += 1
    return res

assert list(add([("a", 1), ("b", 2)], [("a", 1), ("c", 3)])) == [("a", 2), ("b", 2), ("c", 3)]

def sub(xs, ys):
    """Difference two multisets. Return None if the second is not a submultiset of the first"""
    res = []
    i,j = 0,0
    while i < len(xs) and j < len(ys):
        x,n = xs[i]
        y,m = ys[j]
        if x < y:
            res.append((x, n))
            i += 1
        elif x > y:
            return None
        else:
            if n == m:
                pass
            elif n > m:
                res.append((x, n-m))
            else:
                return None
            i += 1
            j += 1
    if j != len(ys):
        return None
    while i < len(xs):
        res.append(xs[i])
        i += 1
    return res

assert sub([("a", 1), ("b", 2)], [("a", 1), ("c", 3)]) is None
assert sub([("a", 1), ("b", 2)], [("a", 1), ("b", 2)]) == []



```

Given these, we can define what it means to have a multiset rewrite rule. We subtract the left hand side of the rule from the multiset. If this is possible (because the multiset is larger than the lhs), we add in the right hand side.

`rewrite` does this iteratively until a fixed point is reached

```python
def replace(xs, lhs, rhs):
    z = sub(xs,lhs)
    if z is None:
        return None
    else:
        return add(z, rhs)

assert replace([("a", 1), ("b", 2)], [("a", 1)], [("a", 2), ("c", 3)]) == [("a", 2), ("b", 2), ("c", 3)]
assert replace([("a", 1), ("b", 2)], [("a", 1), ("b", 2)], [("a", 2), ("c", 3)]) == [("a", 2), ("c", 3)]
assert replace([("a", 1), ("b", 2)], [("a", 1), ("b", 4)], [("a", 2)]) == None
assert replace([('p', 25)], [('p', 25)], [('q', 1)]) == [('q', 1)]

def rewrite(s, R):
    done = False
    while not done:
        done = True
        for i,(lhs,rhs) in enumerate(R):
                s1 = replace(s,lhs,rhs)
                if s1 is not None:
                    s = s1
                    done = False
    return s
```

The next thing we need for completion is a notion of mutliset ordering. This is the analog in grobner bases of a monomial ordering or in term rewriting of a term ordering like knuth bnedix ordering of path ordering.

The ordering I use here is order multisets but size, then tie break lexicogrpahically. This is the analog of the graded lexicographic ordering in grobner bases and shortlex ordering in string rewriting.

```python
def ms_order(xs,ys):
    for (x,n), (y,m) in zip(xs,ys):
        if x < y:
            return ys, xs
        elif x > y:
            return xs, ys
        elif x == y:
            if n < m:
                return ys, xs
            elif n > m:
                return xs, ys
            elif n == m:
                continue
    assert False, "equal multisets"

def count(xs):
    return sum(n for x,n in xs)

# shrinking with ms to tie break. Is this well founded? substitution stable?
# yes, it is graded lex  https://en.wikipedia.org/wiki/Monomial_order#Graded_lexicographic_order
def shortlex(xs,ys):
    cx, cy = count(xs), count(ys)
    if cx < cy:
        return ys, xs
    elif cx > cy:
        return xs, ys
    else:
        return ms_order(xs,ys)

```

Finally, a dumb completion loop. You can do better (Huet style) but this is fine for now. This really is copied basically verbatim from my string rewriting post. <https://www.philipzucker.com/string_knuth/>

```python

def deduce(R):
    """deduce all possible critical pairs from R"""
    for i, (lhs,rhs) in enumerate(R):
        for j in range(i):
            lhs1,rhs1 = R[j]
            o = overlap(lhs1,lhs)
            if o is not None:
                x, y = replace(o, lhs1, rhs1), replace(o, lhs, rhs)
                assert x is not None and y is not None
                if x != y:
                    yield x,y

def KB(E):
    E = E.copy()
    R = []
    done = False
    while not done:
        done = True
        E.extend(deduce(R))
        while E:
            lhs, rhs = E.pop()
            lhs, rhs = rewrite(lhs,R), rewrite(rhs,R)
            if lhs != rhs:
                done = False
                lhs, rhs = shortlex(lhs,rhs)
                R.append((lhs, rhs))
    return R


```

# An example problem

An example problem that I've seen a couple different places is to optimize a change making problem between pennies, quarters, nickels and dimes. This doesn't illuminate the egraph thing, but it does show that our multiset completion is working and the connection to grobner bases and integer programming.

We want 117 cents. Use the fewest coins.

It is quite easy to express this as a mixed integer program

```python
import cvxpy as cvx

p = cvx.Variable(1,"p", integer=True)
n = cvx.Variable(1,"n", integer=True)
d = cvx.Variable(1,"d", integer=True)
q = cvx.Variable(1,"q", integer=True)

constraints = [
    p >= 0,
    n >= 0,
    d >= 0,
    q >= 0,
    p + 5*n + 10*d + 25*q == 117,
]

objective = cvx.Minimize(p + n + d + q)
problem = cvx.Problem(objective, constraints)
print(problem.solve())
d.value, n.value, p.value, q.value

```

    8.0





    (array([1.]), array([1.]), array([2.]), array([4.]))

We can also solve this using grobner bases
<https://mattpap.github.io/masters-thesis/html/src/groebner.html#integer-optimization>

We can see that the exponents of the reduced term are the number of coins of each type.

```python
import sympy as sp
p,n,d,q = sp.var("p n d q")
F = [p**5 - n, p**10 - d, p**25 - q]
G = sp.groebner(F, order='grlex')
print(G)
sp.reduced(p**117, G, order='grlex')[1]
```

    GroebnerBasis([p**5 - n, d**3 - n*q, d**2*n - q, n**2 - d], p, q, d, n, domain='ZZ', order='grlex')

$\displaystyle d n p^{2} q^{4}$

Finally we can also use our multiset completion algorithm. First we get the canonizing rules and then run them on a starting solution of 117 pennies.

```python
def ms(x, n):
    return [(x, n)]

E = [
    (ms("p", 5), ms("n", 1)),
    (ms("p", 10), ms("d", 1)),
    (ms("p", 25), ms("q", 1)),
]

R = KB(E)
# solving the coin problem
assert rewrite(ms("p", 117), R) == [('d', 1), ('n', 1), ('p', 2), ('q', 4)]
```

# Bits and Bobbles

Next time, bolting this into the egraph structure. It is the same thing as bolting in grobner bases.

There is also a sense in which associativity (A), commutativity (I), distributivity (D), and idempotency (I) feel a bit more structural than linearity

Is there a way of bolting linear inequalities into this framework? Graver and Hilbert are in some sense dealing with inequalities and equalities. `Ax=0` `x>=0` normal form of LP problem makes it feel like completion could work.

proofs are also arguably a kind of strucutred eid. I mentioned something like this in the groupoid union find post

Another interesting thing to do is make symbolic lattices or groups that refer back to the egraph to discver their equalities. There was discussion of this way back about whether "merge" functions had to involve primitives or if they could be regular egraph expressions.

4ti2 is a special built system for this sort of thing. They have good fast algorithms probably. It is a command line program. It has some python stuff to write to it. <https://4ti2.github.io/>

I think I need a custom implementation though in order to get intermixing.
Compiling over to gravers / hilbert bases is really confusing.

Graceful usage of structured eids. If you stick to non theory stuff, should fall back to regular union find.

CHR is also multiset rewriting <https://en.wikipedia.org/wiki/Constraint_Handling_Rules> It shows up in other places. CHR book had a chapter on fancy union finds embedding into chr. Is this interesting?

It is interesting that C is trivial to deal with (just sort the arguments to an enode on rebuild), A alone is string rewriting which is not guaranteed to terminate, but A and C together becomes terminating again.

| Axioms  |  Data Structure  | Canon No Theory  | Canon w. Theory |
|---|---|----|---|
| None | Terms    | None |  Egraph / Ground KB |
| C   | sorted terms | sort | Egraph with C enodes |
| A   | Strings   | flatten |  string KB |
| AC  | Multisets | flat and sort | Ground Multiset KB |
| ACI | Sets | dedup | ? |
| ACID | ?  |

A is like path concaternations. Group theory, homotopy
AC is like homology, abelian groups, the abelianization.

There are a couple other systems that are available as normalizers. One of which treats

Discussion of AC and grobner here.
<https://egraphs.zulipchat.com/#narrow/stream/328972-general/topic/Linear.20and.20Polynomial.20Equations/near/454054609>

Pavel Panchekha started an interesting conversation here
<https://egraphs.zulipchat.com/#narrow/stream/328972-general/topic/Is.20WCOJ.20the.20same.20as.20Grobner.20Bases.3F/near/468226525>

Remy asked an insightful questions about how this is any different from greedy destructive rewriting.
"I'm trying to understand what Gröbner buys us over the naïve approach of having a blackbox normalizer, and for every term in the egraph, destructively rewrite that term into with its normal form."

<https://worldscientific.com/doi/abs/10.1142/S0129054192000085?srsltid=AfmBOooNJKz_vsh46RnDAxfdj1hdxoTX0I8Q20qSnLFW1uYIr8LXeqhE>  THE WORD PROBLEM OF ACD-GROUND THEORIES IS UNDECIDABLE - CLAUDE MARCHÉ

![](/assets/ground_theories.png)

<https://www.philipzucker.com/string_knuth/>

<https://mattpap.github.io/masters-thesis/html/src/groebner.html#integer-optimization>

toric grobner bases
toric ideals.
binomials ideals I've also seen?
<https://link.springer.com/chapter/10.1007/3-540-54522-0_102> Buchberger algorithm and integer programming. Conti and Traverso

<https://arxiv.org/pdf/math/0310194> Algebraic Recipes for Integer Programming. Sturmfels

<https://en.wikipedia.org/wiki/Monomial_order>
weighted order is a knuth bendix like order.

could F4 F5 have something to inform knuth bendix /egraphs of?

Hilbert bases vs Graver

Hilbert basis is generating set of cone (positive ocminbation of vector) restriected to lattice points.
Graver is positive orthant + linear equality + integer?

I'm pretty confused on why Quine mcluskey has to do with grobner
x^2 = x
xbar + x = 1

Some Tapas of COmputer Algerba chapter 8
Test Set = vectors for which Ax = 0, st any non optimal solution can have a vector subtracted. Could I find them by enumeration? How would I know when to stop? If we have upper bounds, sure. Maybe I could infer some crude upper bound.

<https://arxiv.org/pdf/2306.06270> markov bases 25 years later.
algerbaic statistics

polynomial optimization and games

<https://4ti2.github.io/>

<https://engineering.purdue.edu/~givan/papers/addct13.pdf> Congruence closure with ACI function symbols

CC (X): Semantic combination of congruence closure with solvable theories
Congruence closure modulo associativity and commutativity
Shostak’s congruence closure as completion.

<https://core.ac.uk/download/pdf/4820666.pdf>  Combining Equational Tree Automata Over AC and ACI Theories?

SO we can pick a symbol per sort to be represented as AC.
Why is that?
Why can't we pick both plus and times? Well, one should use grobner if you have full ring
AC^2
When I merge x*x*x = y + y + y, how am I supposed to resolve this?
_{x,x,x} = +{y,y,y}   but_ + aren't enodes. they're tags.
[(+,1), (x, n)] -> [(*,1), (y,n)]
We just will never generate (+, 3) ?
No this is wrong. Because we might change stuff in a context that. If we have distinct tags, overlap is diallowed.
tagged multisets.
  _(_{a,b}, +{a,a}) = _{a,b,+{a,a}} =>_{a,b,c}, c = +{a,a}
*{x,x,x} = _+{y,y,y}. But we just bake tag matching into the whole thing.
WHat is confusing here...
+({a,a,a}) = c
+[a,a] is an enode
+{a,a,a} is a tagged multiset

so the whole thing becomes ground kb.

union
enode_apply -> generates new enode.
multiset_apply -> maybe generates new enode if tags mismatch but otherwise just merges multisets

structured eclass ids. colors, slots, multisets, polynomials.

```python
! apt install 4ti2
```

```python
%%file /tmp/system.mat
3 2
1 -1
-3 1
1 1
```

    Overwriting /tmp/system.mat

```python
%%file /tmp/system.rel
1 3
< < >
```

    Overwriting /tmp/system.rel

```python
%%file /tmp/system.lhs
1 3
2 1 1
```

    Overwriting /tmp/system.lhs

```python
%%file /tmp/system.sign
1 2
0 1
```

    Writing /tmp/system.sign

```python
!cd /tmp && 4ti2-zsolve system
```

    -------------------------------------------------
    4ti2 version 1.6.9
    Copyright 1998, 2002, 2006, 2015 4ti2 team.
    4ti2 comes with ABSOLUTELY NO WARRANTY.
    This is free software, and you are welcome
    to redistribute it under certain conditions.
    For details, see the file COPYING.
    -------------------------------------------------
    
    Using 32 bit integers.
    
    Linear system to solve:
    
     +  +
     -  0
     F  H
    
     1 -1 <= 0
    -3  1 <= 0
     1  1 >= 0
    
    Linear system of homogeneous equalities to solve:
    
     +  + + +  +
     -  0 0 0  0
     F  H H H  H
    
     1 -1 1 0  0 = 0
    -3  1 0 1  0 = 0
     1  1 0 0 -1 = 0
    
    Lattice:
    
    + +  +  + +
    - 0  0  0 0
    F H  H  H H
    
    1 0 -1  3 1
    0 1  1 -1 1
    
    
    Final basis has 1 inhomogeneous, 3 homogeneous and 0 free elements. Time:  0.00s

```python
!cat /tmp/system.zhom
```

    3 2
    1 3
    1 1
    1 2

```python
!cat /tmp/system.zinhom
```

    1 2
    0 0

```python
class Theory():
    Eid  : type
    def union(self, x : self.EId, y : self.EId):
    def find(self, x):
    def rebuild(self): # kb


```

```python
class FuncDeclRef():
    def __init__(self, name, ctx):
        self.name = name
        self.ctx = ctx
    def __call__(self, *args):
    def __getindex__(self, *args):



# Can we do the 

class EGraph():
    funcdecls : 
    rules : list[tuple[sorts,], fun]

    uf : list[tuple[ms,ms]]
    enodes : dict[ENode, ms]
    def Function(self, name, *sorts):
        return FuncDeclRef(name, self, *sorts)
    
    def union(self, a : ms, b : ms) -> ms:
        pass
    def 
    
    

```

```python
from sage.all import *
from sage.interfaces.four_ti_2 import four_ti_2
four_ti_2.graver([Integer(1),Integer(2),Integer(3)])
```

    ---------------------------------------------------------------------------

    FeatureNotPresentError                    Traceback (most recent call last)

    Cell In[1], line 3
          1 from sage.all import *
          2 from sage.interfaces.four_ti_2 import four_ti_2
    ----> 3 four_ti_2.graver([Integer(1),Integer(2),Integer(3)])


    File /usr/lib/python3/dist-packages/sage/interfaces/four_ti_2.py:418, in FourTi2.graver(self, mat, lat, project)
        398 r"""
        399 Run the 4ti2 program ``graver`` on the parameters. See
        400 ``http://www.4ti2.de/`` for details.
       (...)
        415     [ 2  1  0]
        416 """
        417 project = self._process_input(locals())
    --> 418 self.call('graver', project, options=['-q'])
        419 return self.read_matrix(project+'.gra')


    File /usr/lib/python3/dist-packages/sage/interfaces/four_ti_2.py:299, in FourTi2.call(self, command, project, verbose, options)
        297 import subprocess
        298 feature = FourTi2Executable(command)
    --> 299 feature.require()
        300 executable = feature.executable
        301 options = " ".join(options)


    File /usr/lib/python3/dist-packages/sage/features/__init__.py:206, in Feature.require(self)
        204 presence = self.is_present()
        205 if not presence:
    --> 206     raise FeatureNotPresentError(self, presence.reason, presence.resolution)


    FeatureNotPresentError: 4ti2-graver is not available.
    Executable 'graver' not found on PATH.
    No equivalent system packages for pip are known to Sage.

## Graver

# Graver

<https://fse.studenttheses.ub.rug.nl/11323/1/Masterscriptie.pdf>

lawrence polynomials is the name associated

<https://mattpap.github.io/masters-thesis/html/src/groebner.html#integer-optimization>

graver for MILP
graver for bilevel? It does "domimate" the system, which smells right.

Yeah, fun grobner applications.

Classical feynman diagrams
Mathemtically speaking, quite similar to linkages. These give distance constraints, which are also quadratic.

KKT conditions of LP -> polyunomial ineqs.
Hmm

Hermite matrix

Cody was saying that maybe looking at the guts of simplex might be interesting.
Nearest feasible? Nearest in what sense?

<https://en.wikipedia.org/wiki/Lenstra%E2%80%93Lenstra%E2%80%93Lov%C3%A1sz_lattice_basis_reduction_algorithm>
simulaternous rational approximation
factorizing polynomials with ratiONAL COEFFICIENTS
SOLVING INTEGER PROGRAMING

## Multiset Rewrite / AC / Graver

Bimonomial grobner seems like a match for AC.
This is related to graver via "lawrence polynomials"

a monomial is a multiset of literals.
The different monomial orderings -> different orderings of multisets? Huh

multiset rewriting is string rewriting made commutative. Kind of like homotopy to homology?
abelianization

CHR is non ground mutilset rewriting.

Ground Multiset rewriting

Different representations.

(n,m,k, ...) if we have dense multisets over a finite domain.

```python
from collections import Counter

#type MultiSet = list[tuple[object, int]]
def overlap(xs, ys):
    """Find minimal multiset that is a superset of both xs and ys. Return None if this is just the union (trivial)"""
    nontriv = False
    res = []
    i,j = 0,0
    while i < len(xs) and j < len(ys):
        x,n = xs[i]
        y,m = ys[j]
        if x < y:
            res.append((x, n))
            i += 1
        elif x > y:
            res.append((y, m))
            j += 1
        else:
            nontriv = True
            res.append((x, max(n,m)))
            i += 1
            j += 1
    if not nontriv:
        return None
    while i < len(xs):
        res.append(xs[i])
        i += 1
    while j < len(ys):
        res.append(ys[j])
        j += 1
    return res

assert list(overlap([("a", 1), ("b", 2)], [("a", 1), ("c", 3)])) == [("a", 1), ("b", 2), ("c", 3)]
assert overlap([("a", 1), ("b", 2)], [("c", 1)]) is None

def add(xs,ys):
    """Union two multisets"""
    res = []
    i,j = 0,0
    while i < len(xs) and j < len(ys):
        x,n = xs[i]
        y,m = ys[j]
        if x < y:
            res.append((x, n))
            i += 1
        elif x > y:
            res.append((y, m))
            j += 1
        else:
            res.append((x, n+m))
            i += 1
            j += 1
    while i < len(xs):
        assert j == len(ys)
        res.append((xs[i]))
        i += 1
    while j < len(ys):
        assert i == len(xs)
        res.append((ys[j]))
        j += 1
    return res

assert list(add([("a", 1), ("b", 2)], [("a", 1), ("c", 3)])) == [("a", 2), ("b", 2), ("c", 3)]

# The analog of subseq
def sub(xs, ys):
    """Difference two multisets. Return None if the second is not a submultiset of the first"""
    res = []
    i,j = 0,0
    while i < len(xs) and j < len(ys):
        x,n = xs[i]
        y,m = ys[j]
        if x < y:
            res.append((x, n))
            i += 1
        elif x > y:
            return None
        else:
            if n == m:
                pass
            elif n > m:
                res.append((x, n-m))
            else:
                return None
            i += 1
            j += 1
    if j != len(ys):
        return None
    while i < len(xs):
        res.append(xs[i])
        i += 1
    return res

assert sub([("a", 1), ("b", 2)], [("a", 1), ("c", 3)]) is None
assert sub([("a", 1), ("b", 2)], [("a", 1), ("b", 2)]) == []

def replace(xs, lhs, rhs):
    z = sub(xs,lhs)
    if z is None:
        return None
    else:
        return add(z, rhs)

assert replace([("a", 1), ("b", 2)], [("a", 1)], [("a", 2), ("c", 3)]) == [("a", 2), ("b", 2), ("c", 3)]
assert replace([("a", 1), ("b", 2)], [("a", 1), ("b", 2)], [("a", 2), ("c", 3)]) == [("a", 2), ("c", 3)]
assert replace([("a", 1), ("b", 2)], [("a", 1), ("b", 4)], [("a", 2)]) == None
assert replace([('p', 25)], [('p', 25)], [('q', 1)]) == [('q', 1)]

def rewrite(s, R):
    done = False
    while not done:
        done = True
        for i,(lhs,rhs) in enumerate(R):
                s1 = replace(s,lhs,rhs)
                if s1 is not None:
                    s = s1
                    done = False
    return s

def deduce(R):
    """deduce all possible critical pairs from R"""
    for i, (lhs,rhs) in enumerate(R):
        for j in range(i):
            lhs1,rhs1 = R[j]
            o = overlap(lhs1,lhs)
            if o is not None:
                x, y = replace(o, lhs1, rhs1), replace(o, lhs, rhs)
                assert x is not None and y is not None
                if x != y:
                    yield x,y

def ms_order(xs,ys):
    for (x,n), (y,m) in zip(xs,ys):
        if x < y:
            return ys, xs
        elif x > y:
            return xs, ys
        elif x == y:
            if n < m:
                return ys, xs
            elif n > m:
                return xs, ys
            elif n == m:
                continue
    assert False, "equal multisets"

def count(xs):
    return sum(n for x,n in xs)

# shrinking with ms to tie break. Is this well founded? substitution stable?
# yes, it is graded lex  https://en.wikipedia.org/wiki/Monomial_order#Graded_lexicographic_order
def shortlex(xs,ys):
    cx, cy = count(xs), count(ys)
    if cx < cy:
        return ys, xs
    elif cx > cy:
        return xs, ys
    else:
        return ms_order(xs,ys)


def KB(E):
    E = E.copy()
    R = []
    done = False
    while not done:
        done = True
        E.extend(deduce(R))
        while E:
            lhs, rhs = E.pop()
            lhs, rhs = rewrite(lhs,R), rewrite(rhs,R)
            if lhs != rhs:
                done = False
                lhs, rhs = shortlex(lhs,rhs)
                R.append((lhs, rhs))
    return R

def ms(x, n):
    return [(x, n)]

E = [
    (ms("p", 5), ms("n", 1)),
    (ms("p", 10), ms("d", 1)),
    (ms("p", 25), ms("q", 1)),
]

R = KB(E)
# solving the coin problem
assert rewrite(ms("p", 117), R) == [('d', 1), ('n', 1), ('p', 2), ('q', 4)]

```

```python
class MS():
    def __init__(self, elems):
        self.elems = tuple(sorted(elems))
        sorted(Counter(d).items())

from collections import Counter


def join(d1,d2):
    

# well if we assume sorted, we can do a merge join.
def overlap(dict1,dict2):
    s1 = set(dict1)
    s2 = set(dict2)
    if s1 & s2:
        {k: max(dict1.get(k, 0), dict2.get(k, 0)) 
            for k in s1 | s2}
    else:
        return None


def mergejoin(d1,d2):
    i1 = iter(sorted(d1))
    i2 = iter(sorted(d2))
    k1 = next(i1)
    k2 = next(i2)
    while True:
        if k1 == k2:
            yield k1, max(d1[k1], d2[k2])
            k1 = next(i1)
            k2 = next(i2)
        elif k1 < k2:
            yield k1, d1[k1]
            k1 = next(i1)
        else:
            yield k2, d2[k2]
            k2 = next(i2)

def sub_ms(ms1,ms2):
    pass

def replace(ms, lhs, rhs):
    res = ms.copy()
    for k,v in lhs.items():
        v1 = res.get(k,0)
        if v1 < v:
            return ms
        res[k] = v1 - v
    for k,v in rhs.items():
        res[k] = res.get(k,0) + v
    return res

# rewrite is generic over replace.
def rewrite():
    pass

   # if all( v < ms1[k] if k in ms1 else False for k, v in lhs.items()):
        
    

def complete(E):



    """ 
    if any(x in d1 for x in d2.keys()):
        res = {}
        for x in s2:
            max(d1.get(x, 0)
"""
def overlaps(ms1,ms2):
    # hash join
    d1 = Counter(ms1)
    d2 = Counter(ms2)
    if len(d1) > len(d2):
        d1,d2 = d2,d1
        ms1,ms2 = ms2,ms1
    

        return True


# multiset equations.
def complete(E):

```
