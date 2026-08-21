---
title: Grobner / Buchberger / Knuth Bendix for Semirings and Seven Trees in One
date: 2026-08-21
---

There is a neat paper <https://arxiv.org/abs/math/9405205> Seven Trees in One, where it is shown that there is a nice isomorphism between 7 trees and one tree.

This paper <https://arxiv.org/abs/1208.0538> "Gröbner-Shirshov bases for semirings" uses an automatable technique to derive this fact.

The algebra of types  <https://codewords.recurse.com/issues/three/algebra-and-calculus-of-algebraic-data-types> refers to that tuples and tagged unions behave similarly to the rules of semirings in the sense that two semiring expressions that are equal will be isomorphic types.

Recursive types obey equations. The definition of a binary tree like `data Tree = Lead | Node Tree Tree` is kind of stating the equation `x = 1 + x*x` (there is an ismorphism between x and it's one step unfolding). This equation + semiring axioms implies `x**7 = x`. Pretty cool. The proof of this semiring equality can be interpreted as a type isomorphism.

# Toss it in a Solver

I'll note that fairly impressively, off the shelf automated theorems provers can prove this fact from the semiring axioms pretty quickly.

```python
%%file /tmp/seven.p

cnf(add_zero, axiom, add(zero,Y) = Y).
cnf(add_comm, axiom, add(X,Y) = add(Y,X)).
cnf(add_assoc, axiom, add(X,add(Y,Z)) = add(add(X,Y),Z)).

cnf(one_mul, axiom, mul(X,one) = X).
cnf(zero_mul, axiom, mul(X,zero) = zero).
cnf(mul_comm, axiom, mul(X,Y) = mul(Y,X)).
cnf(mul_assoc, axiom, mul(X,mul(Y,Z)) = mul(mul(X,Y),Z)).

cnf(distrib_left, axiom, mul(X,add(Y,Z)) = add(mul(X,Y),mul(X,Z))).



cnf(tree, axiom, add(one, mul(x,x)) = x). % x**2 + 1 = x
cnf(goal, negated_conjecture, mul(x,mul(x,mul(x,mul(x,mul(x,mul(x,x)))))) != x).
```

    Overwriting /tmp/seven.p

```python
! time vampire --mode casc --intent unsat  --output_mode smtcomp /tmp/seven.p > /dev/null
```

    real 0m1.022s
    user 0m0.981s
    sys 0m0.065s

```python
! time eprover-ho --auto /tmp/seven.p --term-ordering=LPO4 --print-oriented-eqlits-as-rules  --precedence="mul > add > one > zero > x" > /dev/null
```

    real 0m0.606s
    user 0m0.559s
    sys 0m0.046s

```python
! time twee /tmp/seven.p > /dev/null
```

    real 0m0.527s
    user 0m0.475s
    sys 0m0.054s

(In January these were faster, so I'm not sure what happened between now and then)

Nevertheless, despite a lot of fiddling, I was never able to get them to saturate on the non goal directed form of the problem. This is perhaps understandable, since commutativity in particular is unorientable.

It is tempting to try and use an off the shelf buchberger solver, but there's not really a knob to stop them from using negation. One idea was to use different symbols for the left and right side of the equations so that `x^2 + 1 = x` becomes `x^2 + 1 - x1 = 0` and hide the relationship between `x` and `x1`. That is still not sufficient. Once the cat is out of the barn on negation, you can't put it back in.

One thing you can do though is opaquify some things to the solver and inject extra theory derived equations. This is sort of a CEGAR flavored kind of thing. You can use a buchberger solver as a multiset completer <https://www.philipzucker.com/multiset_rw/> . Make each monomial opaque and encode the semiring `+` as the buchberger `*`. Then enhance in a loop with the missing mutliplication equalities.  This could possibly be made to work, but I didn't get far enough.

# Buchberger and Knuth Bendix

Buchberger's algorithm <https://en.wikipedia.org/wiki/Buchberger%27s_algorithm> <https://mattpap.github.io/masters-thesis/html/src/groebner.html> is a methodology for "solving" a system of multinomial equations. It is in some respects a generalization of guassian elimination.

Knuth Bendix completion <https://en.wikipedia.org/wiki/Knuth%E2%80%93Bendix_completion_algorithm> most typically means a method for "solving" a system of term equations (abstracts syntax trees with variables in them) by turning them into normalizing rewrite rules.

The two are basically the same thing in that they are more or less both instances of "abstract completion" (See Term Rewriting and All That (TRAAT) chapter 7).

You are working over some kind of "thing" (terms, polynomials, strings, other) that you have equations form  That "thing" has a way of defining an ordering on it, maybe some notion of context that you can plug things into, some notion of pattern or subterm finding. I'd like to say I know exactly what python / rust / whatever interface I want "thing" to have, but I don't. It probably contains some or all or more of these operations.

Anyway there is a dumb loop you can write which tries to convert thing equations into oriented well founded thing rewrites. Reduce the equations with respect to the current rewrites. Pick an equation and orient it. Generate all overlaps of left hand sides of rewrites as new equations. repeat.

All of this is kind of agnostic to the details of the "thing" you're equations are over.

# Semiring Buchberger

Semirings are rings without negation. Subtraction is partial

It's not an outraegous amount of work to just make a bespoke KB /bucheerger thing for semirings. I have an attention span of about 15 minutes though and there is just step after step of slunky subproblems to solve. This blog post sat on the shelf for 6 months - year. Today, I centaured it with an AI and man it just became so easy. What is the world?
I am a little uncomfortable with out definition of overlap, but otherwise it seems reasonable.

One representation of multisets is sorted lists/tuples. It's a convenient one.

```python
from dataclasses import dataclass, field
from collections import Counter
from typing import ClassVar, Optional


class MS(tuple):
    # multiset
    def __new__(cls, xs=()):
        return super().__new__(cls, sorted(xs))

    def __lt__(self, other):
        return (len(self), tuple(self)) < (len(other), tuple(other))
```

Monomials like `a^2 * b` can be represented as a multiset `{a, a, b}`

A basic semiring datatype is a multiset of monomials. We can overload addition and multiplication on them, which have delightfully succinct implementations. zero can be represented as `{}` and one is `{{}}`, two is `{{}, {}}`, etc. There is no way to represent a negative number.

A lot of this is other convenient overloads. `__sub__` is partial.

During completion you want to examine all terms that may go in two different ways when you apply two rules. All possible failure of confluence. You can generate these from the lhs of rules via overlaps.

In regular buchberger, the single S-polynomial generated as an overlap of the two leading monomials is sufficient. For semirings it is not and there may be more than one nontrivial overlap, as is the case in term or string knuth bendix.

The notion of context (a place inside an expression) for polynomials is `q * _ + r`. You can plug a polynomial into this context. I think returning the context pairs from overlaps is a nice api. Cody seemed to disagree but I'm not sure I understand his objection. He likes the version that returns critical pairs, but that requires giving overlaps the right hand sides also and let it do the plugging.

```python
@dataclass
class Semi:
    outer_order: ClassVar[str] = "multilex"
    monoms: MS[MS[str]] = field(default_factory=MS)

    def __post_init__(self):
        self.monoms = MS(MS(m) for m in self.monoms)

    @staticmethod
    def lit(name) -> "Semi":
        return Semi([[name]])

    @staticmethod
    def of_int(n: int) -> "Semi":
        assert n >= 0
        if n == 0:
            return Semi([])
        elif n == 1:
            return Semi([[]])
        else:
            return Semi([[]]) + Semi.of_int(n - 1)

    def __add__(self, other: "Semi") -> "Semi":
        if isinstance(other, int):
            other = Semi.of_int(other)
        return Semi(MS((MS(self.monoms + other.monoms))))

    def __radd__(self, other: int) -> "Semi":
        return Semi.of_int(other) + self

    def __pow__(self, n: int) -> "Semi":
        assert n >= 0
        if n == 0:
            return Semi.of_int(1)
        result = self
        for _ in range(n - 1):
            result *= self
        return result

    def __mul__(self, other: "Semi") -> "Semi":
        return Semi(MS(MS(m1 + m2) for m1 in self.monoms for m2 in other.monoms))

    def __rmul__(self, other: int) -> "Semi":
        return Semi.of_int(other) * self

    def __repr__(self) -> str:
        return " + ".join([" ".join(m) if m else "1" for m in self.monoms])

    def __lt__(self, other: "Semi") -> bool:
        if Semi.outer_order == "multilex":
            return tuple(reversed(self.monoms)) < tuple(reversed(other.monoms))
        return self.monoms < other.monoms

    def __sub__(self, other: "Semi") -> Optional["Semi"]:
        res = list(self.monoms)
        for m in other.monoms:
            if m in res:
                res.remove(m)
            else:
                return None
        return Semi(MS(res))

    def divrem(self, other: "Semi") -> tuple["Semi", "Semi"]:
        # returns largest q such that self = q*other + r
        assert isinstance(other, Semi)
        if len(other.monoms) == 0:
            raise ValueError("division by zero")
        q = []
        r = self
        lm = other.monoms[-1]
        i = len(r.monoms) - 1
        while i >= 0:
            qm = list(r.monoms[i])
            for x in lm:
                if x not in qm:
                    break
                qm.remove(x)
            else:
                term = Semi([qm])
                r1 = r - term * other
                if r1 is not None:
                    q.append(MS(qm))
                    r = r1
                    i = len(r.monoms) - 1
                    continue
            i -= 1
        return Semi(q), r

    def overlaps(self, other) -> list["Semi"]:
        # return all nontrivial overlaps of self and other
        # such that ov = q1 * self + r1 and ov = q2 * other + r2
        # ov is less that lm(self) * lm(other) ?
        res = []
        for (q, r), _ in self.overlaps_qr(other):
            ov = q * self + r
            if ov not in res:
                res.append(ov)
        return res

    def overlaps_qr(
        self, other
    ) -> list[tuple[tuple["Semi", "Semi"], tuple["Semi", "Semi"]]]:
        # Polynomial contexts split additively, so align one monomial occurrence.
        res = []
        for m1 in Counter(self.monoms):
            for m2 in Counter(other.monoms):
                cm = Counter(m1) | Counter(m2)
                qm1 = MS((cm - Counter(m1)).elements())
                qm2 = MS((cm - Counter(m2)).elements())
                q1, q2 = Semi([qm1]), Semi([qm2])
                t1, t2 = q1 * self, q2 * other
                ov = Semi((Counter(t1.monoms) | Counter(t2.monoms)).elements())
                qr = ((q1, ov - t1), (q2, ov - t2))
                if qr not in res:
                    res.append(qr)
        return res


```

Overlaps is the weirdest one.
We're looking for small polynomials that contain both in interesting ways.

To say they overlap is to have there be `q1,q2,r1,r2` such that.
`ov = q1*p1 + r = q2*p2 + r2`

We only have to consider `q1` that are monomials since the other overlaps are generated by them.
When the overlap occurs, there has to be a monomial in ov that has pieces coming from both p1 and p2. This must come from one of the monomials in p1 and p2. So we can search over all possible pairings on monomials in p1 and p2, find their least common multiple `cm = lcm(m1,m2) = q1 * m1 = q2 * m2`
Then we take `multisetmax(q1*p1, q2*p2)` to make sure that subtraction `r1 = ov - q1 * p1` and `r2 = ov - q2 * p2` from the overlap are defined.

You can see the difference here with the self overlap of `1 + x*x`. S-polynomial overlap would not consider the second one where the `1` is overlapping the `x**2`. `1 + x**2 + x**4 = x**2 * (1 + x**2) + 1 = 1 * (1 + x**2) + x**4`

```python
x = Semi.lit("x")
(x*x+1).overlaps(x*x + 1)
```

    [1 + x x, 1 + x x + x x x x]

Then we have the fairly generic basic completion machinery. We want to represent equations and rewrites. We need an ability to reduce a term with respect to rewrites

```python
@dataclass(frozen=True, slots=True)
class Eq: 
    lhs: Semi
    rhs: Semi


@dataclass(slots=True)
class Rewrite: 
    lhs: Semi
    rhs: Semi
    mark: bool = False

    def __init__(self, lhs: Semi, rhs: Semi, mark: bool = False):
        if lhs < rhs:
            lhs, rhs = rhs, lhs
        self.lhs, self.rhs, self.mark = lhs, rhs, mark

    def __str__(self) -> str:
        return f"{self.lhs} -> {self.rhs}"

type Rewrites = list[Rewrite]


def reduce(semi: Semi, rewrites: Rewrites) -> Semi:
    while True:
        for rw in rewrites:
            q, r = semi.divrem(rw.lhs)
            res = q * rw.rhs + r
            if res != semi:
                semi = res
                break
        else:
            return semi

# some examples
x = Semi.lit("x")
assert reduce(x*x*x, [Rewrite(x*x + 1, x)])      == x*x*x # shouldn't apply because can't subtract 1
assert reduce(x*x*x + x, [Rewrite(x*x + 1, x)])  == x * x # does apply
assert reduce((x*x+1)**3, [Rewrite(x*x + 1, x)]) == x**3
```

Naive completion doesn't reduce previously derived rules. It's quite slow, but straightforward

```python

def naive_complete(eqs: list[Eq]) -> list[Rewrite]:
    # naive completion algorithm
    pending = list(eqs)
    rws = []
    # in loop, reduce equations and add reduced oreitned form to rewrites
    while pending:
        eq = pending.pop(0)
        lhs, rhs = reduce(eq.lhs, rws), reduce(eq.rhs, rws)
        if lhs == rhs:
            continue
        rw = Rewrite(lhs, rhs)
        if rw in rws:
            continue
        # add all overlaps of rewrite lhs to equations
        rules = rws + [rw]
        for rw1 in rules:
            for (q, r), (q1, r1) in rw.lhs.overlaps_qr(rw1.lhs):
                lhs = reduce(q * rw.rhs + r, rules)
                rhs = reduce(q1 * rw1.rhs + r1, rules)
                eq = Eq(lhs, rhs)
                if lhs != rhs and eq not in pending:
                    pending.append(eq)
        rws.append(rw)
    return rws



```

I have a huet style loop I took from chapter 7 of TRAAT. Two variants. One doesn't use marking because it feels funky. One does, which reduced some unnecessary critical pairs. They perform similarly with the marked being a bit faster.

```python

def huet_complete(eqs: list[Eq]) -> list[Rewrite]:
    # huet completion algorithm without marking
    # similar to previous
    # keep equations
    E, R = list(eqs), []
    while True:
        # reduce lhs, rhs according to R
        while E:
            eq = E.pop()
            lhs, rhs = reduce(eq.lhs, R), reduce(eq.rhs, R)
            if lhs == rhs:
                continue
            rw = Rewrite(lhs, rhs)

            # collapse old left sides and compose old right sides
            R1 = [rw]
            for rw1 in R:
                lhs1 = reduce(rw1.lhs, [rw])
                if lhs1 == rw1.lhs:
                    rhs1 = reduce(rw1.rhs, R + [rw])
                    if rw1.lhs != rhs1:
                        R1.append(Rewrite(rw1.lhs, rhs1))
                else:
                    E.append(Eq(lhs1, rw1.rhs))
            R = R1

        # create all critical pairs; marking would avoid redoing old pairs
        for i, rw in enumerate(R):
            for rw1 in R[: i + 1]:
                for (q, r), (q1, r1) in rw.lhs.overlaps_qr(rw1.lhs):
                    lhs = reduce(q * rw.rhs + r, R)
                    rhs = reduce(q1 * rw1.rhs + r1, R)
                    eq = Eq(lhs, rhs)
                    if lhs != rhs and eq not in E:
                        E.append(eq)
        if not E:
            return R


def huet_marked(eqs: list[Eq]) -> list[Rewrite]:
    # the same as the above, but keep a bool in rewrite indicating if it is marked
    # the critical pair generation process picks one unwarked rules and generates critical pairs with all other rules, marking the rule after generating its critical pairs
    # if there are no unmarked rules, the algorithm terminates
    E, R = list(eqs), []
    while True:
        while E:
            eq = E.pop()
            lhs, rhs = reduce(eq.lhs, R), reduce(eq.rhs, R)
            if lhs == rhs:
                continue
            rw = Rewrite(lhs, rhs)

            R1 = [rw]
            for rw1 in R:
                lhs1 = reduce(rw1.lhs, [rw])
                if lhs1 == rw1.lhs:
                    rhs1 = reduce(rw1.rhs, R + [rw])
                    if rw1.lhs != rhs1:
                        R1.append(Rewrite(rw1.lhs, rhs1, rw1.mark))
                else:
                    E.append(Eq(lhs1, rw1.rhs))
            R = R1

        for rw in R:
            if not rw.mark:
                break
        else:
            return R

        rw.mark = True
        for rw1 in R:
            for (q, r), (q1, r1) in rw.lhs.overlaps_qr(rw1.lhs):
                lhs = reduce(q * rw.rhs + r, R)
                rhs = reduce(q1 * rw1.rhs + r1, R)
                eq = Eq(lhs, rhs)
                if lhs != rhs and eq not in E:
                    E.append(eq)
```

```python
x = Semi.lit("x")
print([str(r) for r in huet_marked([Eq(x**2 + 1, x)])])
rws = huet_marked([Eq(x**2 + 1, x)])
reduce(x**7, rws)
```

    ['x x x x x -> 1 + x x x x', '1 + x x x + x x x x -> x x x x', '1 + x x x + x x x -> x x x', 'x + x x x x -> 1 + x x x', '1 + x x -> x']





    x

The Leinster and Fiore rules coming from `x*2 + x + 1 = x` are also derivable.

```python
x = Semi.lit("x")
[str(r) for r in huet_marked([Eq(x**2 + x + 1, x)])]

```

    ['x x x x -> 1 + 1 + x x',
     '1 + x x + x x x -> x x x',
     '1 + x x + x x -> x x',
     'x + x x x -> 1 + x x',
     '1 + x + x x -> x']

# Bits and Bobbles

Semirings are rings (polynomials) where you don't have negation or generally subtraction. The naturals are an example (as compared to the integers).

Removing inverses is useful and changes the game. The less axioms you require, the more places the resulting theorems or system applies.

One talks about the "algebra of types" sometimes in that tuples are like products and tagged unions are like sums. The other laws of semirings apply in the sense that type isomorphisms `tuple[A,B] ~ tuple[B,A]` obey semiring like laws.

This is interesting as a basis for an engine of automated data structure refactoring.

It's also interesting because recursive types obey equations like `list[Bool] ~ bool * list[Bool] + nil` (there is an isomorphism between a list and unfolding it once). These are the sorts of equations that might occur in quotient semiring kind of situations.

This is also the closest point where some funky type theory stuff meets ordinary algebra. Linear equational systems and polynomials do have a notion of proof object. A proof object of a linear system of equations is a vector describing how to add the rows to get the desired goal equation. Polynomials have a similar sort of thing. There is also structure amongst the proofs. They may have a span or multi dimensions. In polynomials there is syzygies and free resolution stuff. This sort of iterated proof object thing is evocative of the concerns of modern dependent type theory.

<https://proofassistants.stackexchange.com/questions/1814/seven-trees-in-one-or-how-to-formalie-the-semiring-of-types>
<https://ncatlab.org/nlab/show/seven+trees+in+one>

The proof producgin version

Do I have to have 1?  {{}} is one

Ok, compressed representation is probably a good idea. (count, monom)

"-a" + "a" = 0   gives us back rings so we can compare to a buchberger (msolve)
"a" -> "-a"

If we only have binary equations
a*a*a = a*a
or
 a + a + a = a + a
it should be a multiset solver
The first is also true for buchberger (no division), but the latter is not true for buchberger (there is subtraction)

parse the msolve format?

```
x,y,z
0
x+2*y+2*z-1,
x^2+2*y^2+2*z^2-x,
2*x*y+2*y*z-y
```

Use their examples. Interpret - as rhs and + as lhs
And we can choose to postulate negatives or not.

I suppose commutativity could be flipped off and turn it into a string solver?

Wait, why was I even using len lex? Is that even an acceptable ordering?
Yes, lenlex is kind a total degree ordering on the inner, but it would be more typical to use a regular multiset on the + multiset

I wonder is sorting rewrites is worth it. Or struct of arrays
Rewrites {
    lhs : Vec<>,
    rhs : Vec<>
    mark : Vec<bool>
}
u32 for variables seems extravagant. u16 or u8 would usually be fine.

Cody disapproved of the ctx pair idea
f(g(x), x) -> x and f(z, g(y)) -> z

(hole,  {x -> g(y)} )  (hole, z -> g(x))

(ctx, subst), (ctx, subst)  the overlap should map into a new third variable space

```python
from semi import *

a,one,zero = Semi.lit("a"), Semi.of_int(1), Semi.of_int(0)
a**2 + 1
[str(r) for r in huet_marked([Eq(a**2 + 1, a)])]
```

    ['a a a a a -> 1 + a a a a',
     '1 + a a a + a a a a -> a a a a',
     '1 + a a a + a a a -> a a a',
     'a + a a a a -> 1 + a a a',
     '1 + a a -> a']

```python
(3*a).overlaps(2*a)
```

    [a + a + a]

```python
(a*a + 1).overlaps(a*a + 1)
```

    [1 + a a + a a a a]

```python
huet_marked([Eq(a + a**2 + 1, a)])
```

    [Rewrite(lhs=a a a a a, rhs=a, mark=True),
     Rewrite(lhs=a a a a + a a a a, rhs=1 + a a a a, mark=True),
     Rewrite(lhs=1 + 1 + a a, rhs=a a a a, mark=True),
     Rewrite(lhs=a a a + a a a a, rhs=1 + a a a, mark=True),
     Rewrite(lhs=1 + a a + a a a, rhs=a a a, mark=True),
     Rewrite(lhs=1 + a a + a a, rhs=a a, mark=True),
     Rewrite(lhs=a + a a a a, rhs=1 + a, mark=True),
     Rewrite(lhs=a + a a a, rhs=1 + a a, mark=True),
     Rewrite(lhs=1 + a + a a, rhs=a, mark=True)]

```python
Semi.out_order = "multilex"
huet_marked([Eq(a + a**2 + 1, a)])
```

    [Rewrite(lhs=a a a a, rhs=1 + 1 + a a, mark=True),
     Rewrite(lhs=1 + a a + a a a, rhs=a a a, mark=True),
     Rewrite(lhs=1 + a a + a a, rhs=a a, mark=True),
     Rewrite(lhs=a + a a a, rhs=1 + a a, mark=True),
     Rewrite(lhs=1 + a + a a, rhs=a, mark=True)]

Huet is signifcantly faster than naive completion. makes sense. That's why one does it

```python
%%time
huet_marked([Eq(a**2 + 1, a)])
```

    CPU times: user 447 ms, sys: 0 ns, total: 447 ms
    Wall time: 446 ms





    [Rewrite(lhs=1 + a a a a, rhs=a a a a a, mark=True),
     Rewrite(lhs=a a a a a a + a a a a a a, rhs=1 + a a a a a a, mark=True),
     Rewrite(lhs=a a a a a a a, rhs=a, mark=True),
     Rewrite(lhs=a a a a a + a a a a a a, rhs=1 + a a a a a, mark=True),
     Rewrite(lhs=a + a a a a a a, rhs=1 + a, mark=True),
     Rewrite(lhs=1 + a a a + a a a, rhs=a a a, mark=True),
     Rewrite(lhs=1 + 1 + a a a, rhs=a a a a a a, mark=True),
     Rewrite(lhs=a + a a a a, rhs=1 + a a a, mark=True),
     Rewrite(lhs=1 + a a, rhs=a, mark=True)]

```python
%%time
naive_complete([Eq(a**2 + 1, a)])
```

    CPU times: user 28 s, sys: 1.98 ms, total: 28 s
    Wall time: 28.1 s





    [Rewrite(lhs=1 + a a, rhs=a, mark=False),
     Rewrite(lhs=a + a a a a, rhs=1 + a a a, mark=False),
     Rewrite(lhs=1 + a a a + a a a, rhs=a a a, mark=False),
     Rewrite(lhs=1 + 1 + a a a, rhs=a + a a a a a, mark=False),
     Rewrite(lhs=1 + a a a + a a a a a a a, rhs=a a + a a a a a a, mark=False),
     Rewrite(lhs=a + a a a a a + a a a a a, rhs=1 + a a a a a, mark=False),
     Rewrite(lhs=1 + a a a a + a a a a, rhs=a a a a + a a a a a, mark=False),
     Rewrite(lhs=1 + a a a + a a a a, rhs=a a a a, mark=False),
     Rewrite(lhs=a a + a a a a a a + a a a a a a a, rhs=a + a a a a a a a, mark=False),
     Rewrite(lhs=a + a a a a a + a a a a a a + a a a a a a, rhs=1 + a a a a a a + a a a a a a, mark=False),
     Rewrite(lhs=a + a + a a a a a, rhs=a + a a a a a a, mark=False),
     Rewrite(lhs=1 + 1 + a a a a, rhs=1 + a a a a a, mark=False),
     Rewrite(lhs=a + a a a a a a, rhs=1 + a, mark=False),
     Rewrite(lhs=a a + a a a a a a, rhs=a, mark=False),
     Rewrite(lhs=1 + a a a a a a + a a a a a a, rhs=1 + 1 + a a a a a a, mark=False),
     Rewrite(lhs=a + a a a a a a a, rhs=a + a, mark=False),
     Rewrite(lhs=1 + a + a a a a a a a a a a, rhs=a + a a a a a, mark=False),
     Rewrite(lhs=1 + a a a a a a + a a a a a a a, rhs=1 + 1 + a, mark=False),
     Rewrite(lhs=a + a + a a a a a a a a a a, rhs=a a + a a a a a a a a a a a a, mark=False),
     Rewrite(lhs=a + a a a a a a a a a, rhs=a a, mark=False),
     Rewrite(lhs=a + a a a a a a a a + a a a a a a a a, rhs=a + a a + a a, mark=False),
     Rewrite(lhs=1 + a a a a, rhs=a a a a a, mark=False),
     Rewrite(lhs=a + a a a a a a a a a a a a + a a a a a a a a a a a a, rhs=1 + 1 + a, mark=False),
     Rewrite(lhs=a a + a a a a a a a a a, rhs=a a + a a a, mark=False),
     Rewrite(lhs=a a a a a + a a a a a + a a a a a a, rhs=1 + a a a a a + a a a a a, mark=False),
     Rewrite(lhs=a + a + a + a a a a a a a a, rhs=a + a + a + a a, mark=False),
     Rewrite(lhs=a a a a a a + a a a a a a a + a a a a a a a, rhs=1 + a a a a a a a + a a a a a a a, mark=False),
     Rewrite(lhs=1 + 1 + a a a a a a a + a a a a a a a a, rhs=1 + a + a, mark=False),
     Rewrite(lhs=1 + a a a a a a a + a a a a a a a a, rhs=a + a, mark=False),
     Rewrite(lhs=a + a a a a a a a a, rhs=a + a a, mark=False),
     Rewrite(lhs=1 + a a a a a a a + a a a a a a a, rhs=1 + a + a, mark=False),
     Rewrite(lhs=a a a a a + a a a a a a, rhs=1 + a a a a a, mark=False),
     Rewrite(lhs=1 + 1 + a a a a a a a, rhs=1 + 1 + a, mark=False),
     Rewrite(lhs=1 + a a a a a a a, rhs=1 + a, mark=False),
     Rewrite(lhs=1 + a a a a a a a a + a a a a a a a a, rhs=a + a a, mark=False),
     Rewrite(lhs=a a a a a a + a a a a a a, rhs=1 + a a a a a a, mark=False),
     Rewrite(lhs=a a + a a a a a a a a a a a a a, rhs=a + a a a a a a a a a a a a a a, mark=False),
     Rewrite(lhs=1 + a + a a a a a a a a a a a a a, rhs=1 + a + a, mark=False),
     Rewrite(lhs=a + a a a a a a a a a a a a, rhs=1 + a, mark=False),
     Rewrite(lhs=a + a a a a a a a a a a, rhs=1 + a a a, mark=False),
     Rewrite(lhs=1 + 1 + a a a a a a a a, rhs=1 + a, mark=False),
     Rewrite(lhs=1 + a + a a a a a a a a a a a, rhs=1 + a a a a a a, mark=False),
     Rewrite(lhs=a a + a a a a a a a a a a a a, rhs=a, mark=False),
     Rewrite(lhs=a + a a a a a a a a a a a, rhs=a a a a a a, mark=False),
     Rewrite(lhs=a + a a a a a a a a a a a a a, rhs=a + a, mark=False),
     Rewrite(lhs=a + a a + a a a a a a a a a a a a a a a a a, rhs=a, mark=False),
     Rewrite(lhs=1 + a + a a a a a a a a a a a a a a a a, rhs=a a a a a a, mark=False),
     Rewrite(lhs=1 + a + a a a a a a a a a a a a a a, rhs=a + a, mark=False),
     Rewrite(lhs=a + a + a a a a a a a a a a a a a a a a, rhs=a, mark=False),
     Rewrite(lhs=1 + a + a a a a a a a a a a a a a a a, rhs=a, mark=False),
     Rewrite(lhs=a a a a a a a a, rhs=a a, mark=False),
     Rewrite(lhs=a a a a a a a, rhs=a, mark=False)]

```python
class MS(tuple):
    def __new__(cls, xs=()):
        return super().__new__(cls, sorted(xs))

    def __lt__(self, other):
        return (len(self), tuple(self)) < (len(other), tuple(other))
```

```python
from dataclasses import dataclass, field

#class MS(list):
#    def __lt__(self, other):
#        return len(self) < len(other) or (len(self) == len(other) and list.__lt__(self, other))

@dataclass
class Semi:
    monoms : MS[MS[str]] = field(default_factory=MS)

    @staticmethod
    def lit(name) -> "Semi":
        return Semi([[name]])
    def __add__(self, other: "Semi") -> "Semi":
        return Semi(MS((MS(self.monoms + other.monoms))))
    def __mul__(self, other: "Semi") -> "Semi":
        return Semi(MS(MS(m1 + m2) for m1 in self.monoms for m2 in other.monoms))
    def __repr__(self) -> str:
        return " + ".join([" ".join(m) for m in self.monoms])
    def __lt__(self, other: "Semi") -> bool:
        return self.monoms < other.monoms
    def __sub__(self, other: "Semi") -> Optional["Semi"]:
        res = list(self.monoms)
        for m in other.monoms:
            if m in self.monoms:
                res.remove(m)
            else:
                return None
        return Semi(MS(res))
    def divrem(self, other: "Semi") -> tuple["Semi", "Semi"]:
        # returns largest q such that self = q*other + r
        assert isinstance(other, Semi)
        if len(other.monoms) == 0:
            raise ValueError("division by zero")
        q = []
        r = list(self.monoms)
        lm = other.monoms[0] # leading monominal of other
        # no this doesn't seem right.
        while all(x in lm for x in r[0]): # submonomonial
            qm = r.pop(0)
            for x in lm:
                qm.remove(x)
            q.append(MS(qm))
        return Semi(MS(q)), Semi(MS(r))
    def overlaps(self, other) -> list["Semi"]:
        # return all nontrivial overlaps of self and other
        # such that ov = q1 * self + r1 and ov = q2 * other + r2
        # ov is less that lm(self) * lm(other)






a,b,c = Semi.lit("a"), Semi.lit("b"), Semi.lit("c")
a*b*c + b*c
b*c + a*b*c == a*b*c + b*c
e = Semi.lit("e")

# e*a = a, e*b = b, e*c = c  could slam one in there.
@dataclass
class Eq: # It is itself a multiset

    lhs: Semi
    rhs: Semi
    def __init__(self, lhs: Semi, rhs: Semi):
        if lhs > rhs:
            self.lhs, self.rhs = lhs,rhs
        else:
            self.lhs, self.rhs = rhs, lhs
        

Eq(e*a, a)
Eq(a, e*a)

```

    ---------------------------------------------------------------------------

    TypeError                                 Traceback (most recent call last)

    Cell In[18], line 26
         21         return self.monoms < other.monoms
         25 a,b,c = Semi.lit("a"), Semi.lit("b"), Semi.lit("c")
    ---> 26 a*b*c + b*c
         27 b*c + a*b*c == a*b*c + b*c
         28 e = Semi.lit("e")


    Cell In[18], line 17, in Semi.__mul__(self, other)
         16 def __mul__(self, other: "Semi") -> "Semi":
    ---> 17     return Semi(MS(MS(m1 + m2) for m1 in self.monoms for m2 in other.monoms))


    Cell In[14], line 3, in MS.__new__(cls, xs)
          2 def __new__(cls, xs=()):
    ----> 3     return super().__new__(cls, sorted(xs))


    Cell In[18], line 17, in <genexpr>(.0)
         16 def __mul__(self, other: "Semi") -> "Semi":
    ---> 17     return Semi(MS(MS(m1 + m2) for m1 in self.monoms for m2 in other.monoms))


    TypeError: can only concatenate tuple (not "list") to tuple

Idea: speicalize commutativity (which is the shitty one?)  to just add(one, X) = add(X, one), add(zero, X) = add(X, zero), .. Does that help? Is this more orietnable?
Use a lanuage that already has polynomials in normal form? consmul(one,X) consadd() ?

```python
%%file /tmp/semiring.p

%cnf(add_one, axiom, add(one,Y) = add(Y,one)).
%cnf(add_x, axiom, add(x,Y) = add(Y,x)).

cnf(add_zero, axiom, add(zero,Y) = Y).
cnf(add_zero, axiom, add(Y,zero) = Y).

%cnf(add_comm, axiom, add(X,Y) = add(Y,X)).
cnf(add_assoc, axiom, add(X,add(Y,Z)) = add(add(X,Y),Z)).

cnf(one_mul, axiom, mul(X,one) = X).
cnf(one_mul, axiom, mul(one,X) = X).
cnf(zero_mul, axiom, mul(X,zero) = zero).
cnf(zero_mul, axiom, mul(zero,X) = zero).
%cnf(mul_x, axiom, mul(X,Y) = mul(Y,X)).

cnf(mul_assoc, axiom, mul(X,mul(Y,Z)) = mul(mul(X,Y),Z)).
%cnf(mul_comm, axiom, mul(X,Y) = mul(Y,X)).

%cnf(distrib_left, axiom, mul(X,add(Y,Z)) = add(mul(X,Y),mul(X,Z))).
%cnf(distrib_right, axiom, mul(add(X,Y),Z) = add(mul(X,Z),mul(Y,Z))).

%cnf(fake, conjecture, true = false).
cnf(x2, axiom, add(one, mul(x,x)) = x).

```

    Overwriting /tmp/semiring.p

```python
! eprover-ho /tmp/semiring.p --auto --term-ordering=LPO4 --ac-handling=KeepOrientable --precedence="mul > add >  one > zero" --print-saturated --print-oriented-eqlits-as-rules 
```

    % Preprocessing class: FSSSSMSSSSSNFFN.
    % Configuration: G-E--_302_C18_F1_URBAN_RG_S04BN
    % (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = Auto)
    % No SInE strategy applied
    % Search class: FUUPM-FFSF22-SFFFFFNN
    % Configuration: SubtermCWHack
    % Initializing proof state
    % Scanning for AC axioms
    % add is associative
    % mul is associative
    %
    %cnf(i_0_15, plain, (mul(X1,zero)->zero)).
    %
    %cnf(i_0_16, plain, (mul(zero,X1)->zero)).
    %
    %cnf(i_0_11, plain, (add(X1,zero)->X1)).
    %
    %cnf(i_0_13, plain, (mul(X1,one)->X1)).
    %
    %cnf(i_0_10, plain, (add(zero,X1)->X1)).
    %
    %cnf(i_0_14, plain, (mul(one,X1)->X1)).
    %
    %cnf(i_0_18, plain, (add(one,mul(x,x))->x)).
    %
    %cnf(i_0_12, plain, (add(add(X1,X2),X3)->add(X1,add(X2,X3)))).
    %
    %cnf(i_0_17, plain, (mul(mul(X1,X2),X3)->mul(X1,mul(X2,X3)))).
    %
    %cnf(i_0_21, plain, (add(one,add(mul(x,x),X1))->add(x,X1))).
    
    % No proof found!
    % SZS status Satisfiable
    % Processed positive unit clauses:
    cnf(i_0_15, plain, (mul(X1,zero)->zero)).
    cnf(i_0_16, plain, (mul(zero,X1)->zero)).
    cnf(i_0_11, plain, (add(X1,zero)->X1)).
    cnf(i_0_13, plain, (mul(X1,one)->X1)).
    cnf(i_0_10, plain, (add(zero,X1)->X1)).
    cnf(i_0_14, plain, (mul(one,X1)->X1)).
    cnf(i_0_18, plain, (add(one,mul(x,x))->x)).
    cnf(i_0_12, plain, (add(add(X1,X2),X3)->add(X1,add(X2,X3)))).
    cnf(i_0_17, plain, (mul(mul(X1,X2),X3)->mul(X1,mul(X2,X3)))).
    cnf(i_0_21, plain, (add(one,add(mul(x,x),X1))->add(x,X1))).
    
    % Processed negative unit clauses:
    
    % Processed non-unit clauses:
    
    % Unprocessed positive unit clauses:
    
    % Unprocessed negative unit clauses:
    
    % Unprocessed non-unit clauses:
    
    

```python

```

# 2026-01

```python
%%file /tmp/semiring.p

cnf(add_comm, axiom, add(X,Y) = add(Y,X)).
cnf(add_assoc, axiom, add(X,add(Y,Z)) = add(add(X,Y),Z)).

cnf(mul_comm, axiom, mul(X,Y) = mul(Y,X)).
cnf(mul_assoc, axiom, mul(X,mul(Y,Z)) = mul(mul(X,Y),Z)).
cnf(distr_left, axiom, mul(X,add(Y,Z)) = add(mul(X,Y),mul(X,Z))).
cnf(distr_right, axiom, mul(add(X,Y),Z) = add(mul(X,Z),mul(Y,Z))).

% let's not have zero or full definition of constants. add(one,one) will be unary
% This maybe let's it avoid getting lost in hte weeds. what use is zero?

cnf(mulone, axiom, mul(one,X) = X).

cnf(x2_1, axiom, x = add(one, mul(x,x))).
% it can prove this
%cnf(goal, negated_conjecture, mul(x,mul(x,mul(x,mul(x,mul(x,mul(x,x)))))) != x).

```

    Overwriting /tmp/semiring.p

--auto -t lpo4   mul > add > one > x finds proof extremely fast. 0.02s

```python
! eprover-ho  --silent  --term-ordering=LPO4 --precedence="mul > add > one > x" --print-saturated /tmp/semiring.p  --print-oriented-eqlits-as-rules 
```

    % (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = (null))
    ^C

```python
!
```

```python
%%file /tmp/semiring.p

cnf(add_comm, axiom, add(X,Y) = add(Y,X)).
cnf(add_assoc, axiom, add(X,add(Y,Z)) = add(add(X,Y),Z)).

cnf(add_zero, axiom, add(X,z) = X).
cnf(add_succ, axiom, add(X,s(Y)) = s(add(X,Y))).


cnf(mul_comm, axiom, mul(X,Y) = mul(Y,X)).
cnf(mul_assoc, axiom, mul(X,mul(Y,Z)) = mul(mul(X,Y),Z)).
cnf(distr_left, axiom, mul(X,add(Y,Z)) = add(mul(X,Y),mul(X,Z))).
cnf(distr_right, axiom, mul(add(X,Y),Z) = add(mul(X,Z),mul(Y,Z))).
cnf(one_mul, axiom, mul(X,s(z)) = X).

cnf(mul_zero, axiom, mul(X,z) = z).
cnf(mul_succ, axiom, mul(X,s(Y)) = add(mul(X,Y),X)).

%cnf(pow_succ, axiom, pow(X,s(Y)) = mul(pow(X,Y),X)).
%cnf(pow_zero, axiom, pow(X,z) = s(z)).


%cnf(pow_x_7, )
%cnf(x2_1, axiom, x = add(s(z), mul(x,x))).
```

    Overwriting /tmp/semiring.p

```python
! eprover-ho  --silent  --term-ordering=LPO4 --precedence="mul > add > s > z" --print-saturated /tmp/semiring.p # --print-oriented-eqlits-as-rules 
```

    % (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = (null))
    
    % No proof found!
    % SZS status Satisfiable
    % Processed positive unit clauses:
    cnf(i_0_14, plain, (add(X1,z)=X1)).
    cnf(i_0_21, plain, (mul(X1,z)=z)).
    cnf(i_0_23, plain, (add(z,X1)=X1)).
    cnf(i_0_28, plain, (mul(z,X1)=z)).
    cnf(i_0_15, plain, (add(X1,s(X2))=s(add(X1,X2)))).
    cnf(i_0_22, plain, (mul(X1,s(X2))=add(X1,mul(X1,X2)))).
    cnf(i_0_13, plain, (add(add(X1,X2),X3)=add(X1,add(X2,X3)))).
    cnf(i_0_50, plain, (add(s(X1),X2)=s(add(X1,X2)))).
    cnf(i_0_17, plain, (mul(mul(X1,X2),X3)=mul(X1,mul(X2,X3)))).
    cnf(i_0_86, plain, (mul(s(X1),X2)=add(X2,mul(X1,X2)))).
    cnf(i_0_18, plain, (mul(X1,add(X2,X3))=add(mul(X1,X2),mul(X1,X3)))).
    cnf(i_0_19, plain, (mul(add(X1,X2),X3)=add(mul(X1,X3),mul(X2,X3)))).
    cnf(i_0_12, plain, (add(X1,X2)=add(X2,X1))).
    cnf(i_0_16, plain, (mul(X1,X2)=mul(X2,X1))).
    cnf(i_0_47, plain, (add(X1,add(X2,X3))=add(X3,add(X1,X2)))).
    cnf(i_0_54, plain, (add(X1,add(X2,X3))=add(X2,add(X1,X3)))).
    cnf(i_0_63, plain, (mul(X1,mul(X2,X3))=mul(X3,mul(X1,X2)))).
    cnf(i_0_70, plain, (mul(X1,mul(X2,X3))=mul(X2,mul(X1,X3)))).
    cnf(i_0_146, plain, (add(X1,add(X2,X3))=add(X3,add(X2,X1)))).
    cnf(i_0_228, plain, (mul(X1,mul(X2,X3))=mul(X3,mul(X2,X1)))).
    
    % Processed negative unit clauses:
    
    % Processed non-unit clauses:
    
    % Unprocessed positive unit clauses:
    
    % Unprocessed negative unit clauses:
    
    % Unprocessed non-unit clauses:
    
    

```python
%%file /tmp/seven.p
cnf(i_0_14, plain, (add(X1,z)=X1)).
cnf(i_0_21, plain, (mul(X1,z)=z)).
cnf(i_0_23, plain, (add(z,X1)=X1)).
cnf(i_0_28, plain, (mul(z,X1)=z)).
cnf(i_0_15, plain, (add(X1,s(X2))=s(add(X1,X2)))).
cnf(i_0_22, plain, (mul(X1,s(X2))=add(X1,mul(X1,X2)))).
cnf(i_0_13, plain, (add(add(X1,X2),X3)=add(X1,add(X2,X3)))).
cnf(i_0_50, plain, (add(s(X1),X2)=s(add(X1,X2)))).
cnf(i_0_17, plain, (mul(mul(X1,X2),X3)=mul(X1,mul(X2,X3)))).
cnf(i_0_86, plain, (mul(s(X1),X2)=add(X2,mul(X1,X2)))).
cnf(i_0_18, plain, (mul(X1,add(X2,X3))=add(mul(X1,X2),mul(X1,X3)))).
cnf(i_0_19, plain, (mul(add(X1,X2),X3)=add(mul(X1,X3),mul(X2,X3)))).
cnf(i_0_12, plain, (add(X1,X2)=add(X2,X1))).
cnf(i_0_16, plain, (mul(X1,X2)=mul(X2,X1))).
cnf(i_0_47, plain, (add(X1,add(X2,X3))=add(X3,add(X1,X2)))).
cnf(i_0_54, plain, (add(X1,add(X2,X3))=add(X2,add(X1,X3)))).
cnf(i_0_63, plain, (mul(X1,mul(X2,X3))=mul(X3,mul(X1,X2)))).
cnf(i_0_70, plain, (mul(X1,mul(X2,X3))=mul(X2,mul(X1,X3)))).
cnf(i_0_146, plain, (add(X1,add(X2,X3))=add(X3,add(X2,X1)))).
cnf(i_0_228, plain, (mul(X1,mul(X2,X3))=mul(X3,mul(X2,X1)))).
cnf(x2_1, axiom, x = add(s(x), mul(x,x))).
cnf(mygoal, negated_conjecture, mul(x,mul(x,mul(x,mul(x,mul(x,mul(x,x)))))) != x).
```

    Overwriting /tmp/seven.p

```python
! eprover-ho --silent   --term-ordering=LPO4 --print-oriented-eqlits-as-rules  --precedence="mul > add > s > z > x" --print-saturated /tmp/seven.p  
```

    % (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = (null))
    ^C

Just make noncommutative gorbner and have grobner as a special case.
Give fully commuting subtstrings names and make them multisets.

interactive knuth bendix was a thing? Get rrl running? kbcv?
<http://cl-informatik.uibk.ac.at/software/kbcv/>

<https://dl.acm.org/doi/10.1145/120694.120701> “One sugar cube, please” or selection strategies in the Buchberger algorithm
<https://github.com/sdiehl/groebner>
"On an installation of Buchberger's algorithm."  <https://www.sciencedirect.com/science/article/pii/S0747717188800488>

Alegrbaic program semantics
Trace Knuth Bendix. partially comutatibe monoid

<https://link.springer.com/article/10.1007/s11424-017-6337-8>  Comprehensive Gröbner basis theory for a parametric polynomial ideal and the associated completion algorithm. This sounds a lot like tensor grobner

<https://arxiv.org/abs/math/0212377> Leinster Fiore
Objects of categories as complex numbers

semiring grobner bases

How to take the inverse of a type
<https://kar.kent.ac.uk/98022/1/LIPIcs-ECOOP-2022-5.pdf> Dominic Orchard `t -o 1` is inv(t)

Is there something to automated here <https://www.sciencedirect.com/science/article/pii/S0021869313001592> ? Gorbner bases for semirings

What about just using twee? Can it do it?

<https://cofault.com/aodt.html>  1/k! is permutation
Nat ~ e
Bag(x) = e^x = x -> Nat = 1 + x + x/2! + ...
Set(x) = 1 + x + x * x(x-1) /2! + ...

"Ring" is necklaces. Ring(x) = -ln(1-x)
deriv Ring = List
Bag(Ring(x)) = List(x)

Brent Yorgey Combinatorial species

<https://drops.dagstuhl.de/storage/00lipics/lipics-vol141-itp2019/LIPIcs.ITP.2019.6/LIPIcs.ITP.2019.6.pdf> Data Types as Quotients of Polynomial Functors - avidgad mario

"non-regular datatypes"
shapely types

Containers
Constructing polymorphic programs with quotient types
M Abbott, T Altenkirch, N Ghani, C McBride -

<https://proofassistants.stackexchange.com/questions/1814/seven-trees-in-one-or-how-to-formalize-the-semiring-of-types>
<https://arxiv.org/pdf/math/9405205> seven trees in one blass

Hmm. Use a grobner basis solver somehow to make useful suggested lemmas?

overlap of a semiring expression would be a common factor.
gcd.
Why is that not as relevant for ring?
<https://en.wikipedia.org/wiki/Greatest_common_divisor>
<https://en.wikipedia.org/wiki/Polynomial_greatest_common_divisor>

R = k[x,y,z]

R^N -> R. The image is the ideal.
`R^N -> R --?-> R/I = {[f]} = {g | f + g = 0 /\ g in I }`
`R^n1 -syzygy> R^n0 -> R`

[ xy, xy+z]
macaulay 2 has incremental grobner (Spair) ?
free resolution of a quotient datatype

```python
%%file /tmp/semiring.p

cnf(add_comm, axiom, add(X,Y) = add(Y,X)).
cnf(add_assoc, axiom, add(X,add(Y,Z)) = add(add(X,Y),Z)).
cnf(mul_comm, axiom, mul(X,Y) = mul(Y,X)).
cnf(one_mul, axiom, mul(X,one) = X).
cnf(mul_assoc, axiom, mul(X,mul(Y,Z)) = mul(mul(X,Y),Z)).
cnf(distrib_left, axiom, mul(X,add(Y,Z)) = add(mul(X,Y),mul(X,Z))).
cnf(distrib_right, axiom, mul(add(X,Y),Z) = add(mul(X,Z),mul(Y,Z))).

cnf(list_poly, axiom, x = add(one, mul(x,x))).  % x = 1 + x^2

%cnf(fake, conjecture, true = false).
fof(seven_tree, conjecture, mul(mul(mul(mul(mul(mul(x,x),x),x),x),x),x) = x). % x^7 = x

%fof(test1, conjecture, mul(add(a,b),c) = add(mul(a,c),mul(b,c))).

```

    Overwriting /tmp/semiring.p

```python
! eprover-ho --auto  /tmp/semiring.p # much slower. 2s. Still does it though
```

```python
! time twee /tmp/semiring.p # instant 0.2s
```

```python
! time vampire --mode casc --print_proofs_to_file /tmp/proof /tmp/semiring.p  # --proof smtcheck --proof_extra full
```

```python
%%file /tmp/fiore.p

cnf(add_comm, axiom, add(X,Y) = add(Y,X)).
cnf(add_assoc, axiom, add(X,add(Y,Z)) = add(add(X,Y),Z)).
cnf(mul_comm, axiom, mul(X,Y) = mul(Y,X)).
cnf(one_mul, axiom, mul(X,one) = X).
cnf(mul_assoc, axiom, mul(X,mul(Y,Z)) = mul(mul(X,Y),Z)).
cnf(distrib_left, axiom, mul(X,add(Y,Z)) = add(mul(X,Y),mul(X,Z))).
cnf(distrib_right, axiom, mul(add(X,Y),Z) = add(mul(X,Z),mul(Y,Z))).

cnf(zero_add, axiom, x = add(one, mul(x,x))).  % x = 1 + x^2
fof(seven_tree, conjecture, mul(mul(mul(mul(mul(mul(x,x),x),x),x),x),x) = x). % x^7 = x

%fof(test1, conjecture, mul(add(a,b),c) = add(mul(a,c),mul(b,c))).

```

```python
from kdrag.all import *

Type = smt.DeclareSort("Type1")
add = smt.Function("add", Type, Type, Type)
mul = smt.Function("mul", Type, Type, Type)
one = smt.Const("one", Type)
kd.notation.add.register(Type, add)
kd.notation.mul.register(Type, mul)
x,y,z = smt.Consts("x y z", Type)
semiring = [kd.axiom(smt.ForAll([x,y], x + y == y + x)),
kd.axiom(smt.ForAll([x,y,z], x + (y + z) == (x + y) + z)),
kd.axiom(smt.ForAll([x,y], x * y == y * x)),
kd.axiom(smt.ForAll([x], x * one == x)),
kd.axiom(smt.ForAll([x,y,z], x * (y * z) == (x * y) * z)),
kd.axiom(smt.ForAll([x,y,z], x * (y + z) == (x * y) + (x * z))),
kd.axiom(smt.ForAll([x,y,z], (x + y) * z == (x * z) + (y * z)))] 

import kdrag.solvers as solvers

#s = solvers.VampireTHFSolver()
s = solvers.TweeSolver()
s.add([p.thm for p in semiring])
s.add(x == one + x * x)  # x = 1 + x^2
s.add(x * x * x * x * x * x * x != x) # x^7 = x
s.check()

```

    ---------------------------------------------------------------------------

    KeyboardInterrupt                         Traceback (most recent call last)

    Cell In[12], line 25
         23 s.add(x == one + x * x)  # x = 1 + x^2
         24 s.add(x * x * x * x * x * x * x != x) # x^7 = x
    ---> 25 s.check()


    File ~/Documents/python/knuckledragger/src/kdrag/solvers/__init__.py:734, in TweeSolver.check(self)
        726 cmd = [
        727     binpath("twee"),
        728     "--tstp",
        729     "/tmp/twee.p",
        730 ]
        731 # if "timeout" in self.options:
        732 #    cmd.extend(["-t", str(self.options["timeout"] // 1000 + 1)])
    --> 734 self.res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        736 return self.check_tptp_status(self.res.stdout)


    File /usr/lib/python3.12/subprocess.py:550, in run(input, capture_output, timeout, check, *popenargs, **kwargs)
        548 with Popen(*popenargs, **kwargs) as process:
        549     try:
    --> 550         stdout, stderr = process.communicate(input, timeout=timeout)
        551     except TimeoutExpired as exc:
        552         process.kill()


    File /usr/lib/python3.12/subprocess.py:1209, in Popen.communicate(self, input, timeout)
       1206     endtime = None
       1208 try:
    -> 1209     stdout, stderr = self._communicate(input, endtime, timeout)
       1210 except KeyboardInterrupt:
       1211     # https://bugs.python.org/issue25942
       1212     # See the detailed comment in .wait().
       1213     if timeout is not None:


    File /usr/lib/python3.12/subprocess.py:2115, in Popen._communicate(self, input, endtime, orig_timeout)
       2108     self._check_timeout(endtime, orig_timeout,
       2109                         stdout, stderr,
       2110                         skip_check_and_raise=True)
       2111     raise RuntimeError(  # Impossible :)
       2112         '_check_timeout(..., skip_check_and_raise=True) '
       2113         'failed to raise TimeoutExpired.')
    -> 2115 ready = selector.select(timeout)
       2116 self._check_timeout(endtime, orig_timeout, stdout, stderr)
       2118 # XXX Rewrite these to use non-blocking I/O on the file
       2119 # objects; they are no longer using C stdio!


    File /usr/lib/python3.12/selectors.py:415, in _PollLikeSelector.select(self, timeout)
        413 ready = []
        414 try:
    --> 415     fd_event_list = self._selector.poll(timeout)
        416 except InterruptedError:
        417     return ready


    KeyboardInterrupt: 

```python
from kdrag.all import *
import functools
T = smt.DeclareSort("Type1")
add = smt.Function("add", T, T, T)
mul = smt.Function("mul", T, T, T)
one = smt.Const("one", T)
zero = smt.Const("zero", T)
kd.notation.add.register(T, add)
kd.notation.mul.register(T, mul)
kd.CommSemiRing(add, mul, zero, one)

s = solvers.VampireSolver()
s.add(kd.CommSemiRing(add, mul, zero, one))
x = smt.Const("x", T)
s.add(x == x * x + one)
#s.add( functools.reduce(mul, [x]*7) != x)
#s.add(smt.RealVal(3) == 2)
s.set("format", "fof")
s.check()
```

    no_mangle: {And, one, mul, zero, ==, x, add}
    {And, X!132, Y!133, one, mul, Z!134, zero, ==, x, add}
    {And, X!132, Y!133, one, mul, Z!134, X!135, zero, Y!136, ==, x, add}
    {And, X!132, Y!133, one, mul, Z!134, X!135, zero, Y!136, X!137, ==, x, add}
    {And, X!132, Y!133, one, mul, Z!134, X!135, zero, Y!136, X!137, X!138, ==, Y!139, x, Z!140, add}
    {And, X!132, Y!133, one, mul, Z!134, X!135, zero, Y!136, X!137, X!138, ==, Y!139, x, Z!140, X!141, add}
    {And, X!132, Y!133, one, mul, Z!134, X!135, zero, Y!136, X!137, X!138, ==, Y!139, x, Z!140, X!141, X!142, add}
    {And, add, one, mul, zero, ==, x, X!132, Y!133, Z!134, X!135, Y!136, X!137, X!138, Y!139, Z!140, X!141, X!142, X!143}
    {And, add, one, mul, zero, ==, x, X!132, Y!133, Z!134, X!135, Y!136, X!137, X!138, Y!139, Z!140, X!141, X!142, X!143, X!144}
    {And, add, one, mul, zero, ==, x, X!132, Y!133, Z!134, X!135, Y!136, X!137, X!138, Y!139, Z!140, X!141, X!142, X!143, X!144, X!145, Y!146, Z!147}
    {And, add, one, mul, zero, ==, x, X!132, Y!133, Z!134, X!135, Y!136, X!137, X!138, Y!139, Z!140, X!141, X!142, X!143, X!144, X!145, Y!146, Z!147, X!148, Y!149, Z!150}
    {And, add, one, mul, zero, ==, x, X!132, Y!133, Z!134, X!135, Y!136, X!137, X!138, Y!139, Z!140, X!141, X!142, X!143, X!144, X!145, Y!146, Z!147, X!148, Y!149, Z!150, X!151, Y!152}

<b>unknown</b>

```python



```

# boolean optimization

see boo,min logic synt

def f2ify()

```python

```

&#x22A8;And(x, y, Or(z, Not(x))) ==
And(x, y, Xor(True, And(Xor(True, z), Xor(True, Not(x)))))

```python
smt.Xor(x,y).decl()
```

Xor

```python




```

    Overwriting /tmp/msolve.ms

```python

```

    [-1]:

```python

```

    [{x: [2.76929235423863 +/- 2.08e-15], y: [0.361103080528647 +/- 4.53e-16]},
     {x: 1.000000000000000, y: 1.000000000000000}]

```python

```

    ---------------------------------------------------------------------------

    ValueError                                Traceback (most recent call last)

    Cell In[3], line 4
          2 x, y = R.gens()
          3 I = Ideal([ x*y - 1, (x-2)**2 + (y-1)**2 - 1])
    ----> 4 I.variety(RBF, algorithm='msolve', proof=False)


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/sage/rings/polynomial/multi_polynomial_ideal.py:308, in RequireField.__call__(self, *args, **kwds)
        306 if not R.base_ring().is_field():
        307     raise ValueError("Coefficient ring must be a field for function '%s'." % (self.f.__name__))
    --> 308 return self.f(self._instance, *args, **kwds)


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/sage/rings/polynomial/multi_polynomial_ideal.py:2713, in MPolynomialIdeal_singular_repr.variety(self, ring, algorithm, proof)
       2711 elif algorithm == "msolve":
       2712     from . import msolve
    -> 2713     return msolve.variety(self, ring, proof=proof)
       2714 else:
       2715     raise ValueError(f"unknown algorithm {algorithm!r}")


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/sage/rings/polynomial/msolve.py:238, in variety(ideal, ring, proof)
        236     ring = base
        237 if not ring.has_coerce_map_from(base):
    --> 238     raise ValueError(
        239         f"no coercion from base field {base} to output ring {ring}")
        241 if isinstance(ring, (RealIntervalField_class, RealBallField,
        242                      RealField_class, RealDoubleField_class)):
        243     parameterization = False


    ValueError: no coercion from base field Finite Field of size 2 to output ring Real ball field with 53 bits of precision

```python
from kdrag.all import *
def assoc(f): # semigroup
    T = f.range()
    x, y, z = smt.Consts("x y z", T)
    return smt.ForAll([x,y,z], f(x, f(y, z)) == f(f(x, y), z))
def semigroup(T):
    mul = smt.Function("mul", T, T, T)
    return assoc(mul, T)
def addsemigroup(T):
    add = smt.Function("add", T, T, T)
    return assoc(add, T)
def comm(f):
    T = f.range()
    x, y = smt.Consts("x y", T)
    return smt.ForAll([x,y], f(x, y) == f(y, x))
def idem(f):
    T = f.range()
    x = smt.Const("x", T)
    return smt.ForAll([x], smt.Eq(f(x, x) == x))
def mul_one(f, one):
    T = one.sort()
    x = smt.Const("x", T)
    return smt.ForAll([x], f(x, one) == x)
def one_mul(f, one, T):
    x = smt.Const("x", T)
    return smt.ForAll([x], f(one, x) == x)
def monoid(T):
    mul = smt.Function("mul", T, T, T)
    one = smt.Const("one", T)
    return smt.And(
        assoc(mul, T),
        mul_one(mul, one, T),
        one_mul(mul, one, T)
    )

def group(T):
    mul = smt.Function("mul", T, T, T)
    one = smt.Const("one", T)
    inv = smt.Function("inv", T, T)
    x,y,z = smt.Consts("x y z", T)
    return smt.And(
        assoc(mul, T),
        one_mul(mul, one, T),
        smt.ForAll([x], mul(x, inv(x)) == one)
    )

T = smt.DeclareSort("Type1")
add = smt.Function("add", T, T, T)
mul = smt.Function("mul", T, T, T)

def semiring(T):
    x,y,z = smt.Consts("x y z", T)
    add = smt.Function("add", T, T, T)
    mul = smt.Function("mul", T, T, T)
    return smt.And(
        comm(add),
        assoc(add),
        comm(mul),
        mul_one(mul, smt.Const("one", T)),
        assoc(mul),
        smt.ForAll([x,y,z], mul(x, add(y, z)) == add(mul(x, y), mul(x, z))),
        smt.ForAll([x,y,z], mul(add(x, y), z) == add(mul(x, z), mul(y, z)))
    )
semiring(smt.RealSort())



class GroupProps():
    def __init__(self, T):
        grp = group(T)


def Lattice(T):
    x,y,z = smt.Consts("x y z", T)
    meet = smt.Function("meet", T, T, T)
    join = smt.Function("join", T, T, T)
    return smt.And(
        comm(meet, T),
        assoc(meet, T),
        comm(join, T),
        assoc(join, T),
        smt.ForAll([x,y], meet(x, join(x, y)) == x),
        smt.ForAll([x,y], join(x, meet(x, y)) == x)
        
    )

Lattice(T)
```

```python
def CompleteSemiLattice(bigjoin):
    # bigjoin : Set[T] -> T
    T = bigjoin.range()
    ST = smt.SetSort(T)
    join = lambda x,y: bigjoin(smt.Store(smt.Store(smt.EmptySet(T), x, True), y, True))
    # join is associative, commutative and idempotent by definition
    le = lambda x,y: join(x,y) == y
    # least upper bound
    x,y = smt.Consts("x y", T)
    A = smt.Const("A", ST)
    return smt.ForAll([x,y,A],
        le(x, y),
        le(bigjoin(A), y)
    )
```

```python
import functools
@functools.cache
def SemiLattice(op):
    T = op.range()
    x,y,z = smt.Consts("x y z", T)
    return kd.define("SemiLattice_"+str(T), smt.And(
        comm(meet, T),
        assoc(meet, T),

    ))
```

```python


```

```python

```

# grobner for semiring

How?
Some kind of cegar? Try grobner, somehow outlaw stuff that doesn't work?
Name positive and negative or left / right side variables as opasque things

Boolean semiring translates to a boolean ring via the xor transformation. Very unusual? Do other GF do this?
Grobner in boolean ring first, translate or use as clues?

lhs = rhs becomes
a *lhs = b* rhs
b *lhs = a* rhs

a *(t1 - t2) = b* (s1 - s2)
The S polynomial forming step. Could then positivize. I just don't think so.
a *p + b* q = a *r + b* d

Finite stepping of the relation?
a0 lhs = a1 rhs
a1 lhs = a2 rhs

Give the left and right different variable names
x*y + 1 = x1* y1
x1 *y1 + 1 = x2* y2

1 + x + x^2 = x generates basis of

x^4 = 1 + 1 + x^2
x+x^3 = 1 + x^2
1 + x^2 + x^n = x^n   1 <= n <= 3

x = 1 + x^2
1 + x^2 = x
x + x^4 = 1 + x^3
x^5 = 1 + x^4
1 + x ^3 + x^n = x^n  3 <= n <= 4

lead * x^3 + x =

1 + x*2 = x

lead + x*2 = x
1 + lead x^2 = x
1 +

(1 + x^2)a = xb
xa =

1 + x^2 has selve overlap 1 + x^2 + x^4

(1 + lead x^2) - x
lead + x^2 - x
S poly would be
1 - x - x^4 +  = 0

trail + lead x^2 - rhs x
lead + trail x^2 - rhs x

x + 1 = y + 1, the 1 shouldn't cancel.

1 + x^2 + x^4
x + x^4 = 1 + x^2 (x) = 1 + x^3

It is easier to see how to embed and abstraction into multsiet rewriting

<https://www.philipzucker.com/multiset_rw/>

Consider each of the monotmials as a atomic thing
1 + x^2 = x  --->  {x0, x2} -> {x1}  
Let it complete. Then add all the other learned overlap identities.
Hmm.
Or add all shifted identities.

Mapping into grobner bases using powers.
x0 * x2  = x1  
but also all shifted versions.

Embedding grobner into linear is a related sort of game? linear but all shifted versions

Embedding semiring into hermite solver?

<https://docs.oscar-system.org/v1/TropicalGeometry/groebner_theory/> tropical grobner.
<https://arxiv.org/abs/0903.5044>  On Groebner Basis in Monoid and Group Rings
<https://arxiv.org/pdf/2401.05731> grobner shirshov for markov semiringsd
<https://www.sciencedirect.com/science/article/pii/S0747717116000183> Resultants over commutative idempotent semirings I: Algebraic aspect

commutative idempotent semiring

<https://arxiv.org/pdf/1609.03838> Tropical Ideals Diane Maclagan and Felipe Rinc´on
I was talking to Nate about grobner for Monoidal-iush stuff. Abelian categories

4ti2 and other hilbert base stuff?
4ti2
Normaliz
polymake

<https://www.philipzucker.com/dump-of-nonlinear-algebra-algebraic-geometry-notes-good-links-though/>

```python
from sage.features.four_ti_2 import FourTi2Executable, FourTi2
FourTi2().is_present()
```

    FeatureTestResult('sage.interfaces.four_ti_2', False)

```python
from sage.all__sagemath_msolve import *
R = PolynomialRing(QQ, 2, names=['x', 'y'], order='lex')
x, y = R.gens()
I = Ideal([ x*y - 1, (x-2)**2 + (y-1)**2 - 1])
I.groebner_basis(algorithm="msolve")
#I.variety(RBF, algorithm='msolve', proof=False)
```

    ---------------------------------------------------------------------------

    KeyError                                  Traceback (most recent call last)

    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/sage/misc/cachefunc.pyx:1970, in sage.misc.cachefunc.CachedMethodCaller.__call__()
       1969 try:
    -> 1970     return cache[k]
       1971 except TypeError:  # k is not hashable


    KeyError: (('msolve', None, None, False), ())

    
    During handling of the above exception, another exception occurred:


    NotImplementedError                       Traceback (most recent call last)

    Cell In[15], line 5
          3 x, y = R.gens()
          4 I = Ideal([ x*y - 1, (x-2)**2 + (y-1)**2 - 1])
    ----> 5 I.groebner_basis(algorithm="msolve")
          6 #I.variety(RBF, algorithm='msolve', proof=False)


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/sage/misc/cachefunc.pyx:1975, in sage.misc.cachefunc.CachedMethodCaller.__call__()
       1973         return cache[k]
       1974 except KeyError:
    -> 1975     w = self._instance_call(*args, **kwds)
       1976     cache[k] = w
       1977     return w


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/sage/misc/cachefunc.pyx:1851, in sage.misc.cachefunc.CachedMethodCaller._instance_call()
       1849         True
       1850     """
    -> 1851     return self.f(self._instance, *args, **kwds)
       1852 
       1853 cdef fix_args_kwds(self, tuple args, dict kwds):


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/sage/rings/qqbar_decorators.py:100, in handle_AA_and_QQbar.<locals>.wrapper(*args, **kwds)
         94 from sage.rings.abc import AlgebraicField_common
         96 if not any(isinstance(a, (Polynomial, MPolynomial, Ideal_generic))
         97            and isinstance(a.base_ring(), AlgebraicField_common)
         98            or isinstance(a, PolynomialSequence_generic)
         99            and isinstance(a.ring().base_ring(), AlgebraicField_common) for a in args):
    --> 100     return func(*args, **kwds)
        102 polynomials = []
        104 for a in flatten(args, ltypes=(list, tuple, set)):


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/sage/rings/polynomial/multi_polynomial_ideal.py:4758, in MPolynomialIdeal.groebner_basis(self, algorithm, deg_bound, mult_bound, prot, *args, **kwds)
       4756 elif algorithm == 'msolve':
       4757     if self.ring().term_order() != 'degrevlex':
    -> 4758         raise NotImplementedError("msolve only supports the degrevlex order "
       4759                                   "(use transformed_basis())")
       4760     if not (deg_bound is mult_bound is None) or prot:
       4761         raise NotImplementedError("unsupported options for msolve")


    NotImplementedError: msolve only supports the degrevlex order (use transformed_basis())

```python
class FreeRig():
    data: tuple[int] # sorted multiset of powers
    def __init__(self, data):
        self.data = tuple(sorted(data))
    def __add__(self, other):
        return FreeRig(self.data + other.data)
    def __mul__(self, other):
        return FreeRig(i + j for i in self.data for j in other.data)
    def overlaps(self, other):
    def divrem(self, other):
        
    
```

drags combine context and vars/subst

```python
class Ctx(Protocol):
    def plug(self, t): ...

#class Rewrite(Protocol):
#    def 

class GroundKB(Protocol):
    def overlaps() -> list[tuple[tuple[Ctx, object], tuple[Ctx, object]]]:
    def 
```

```python
e^(x^2 + 1) = e^(c * x^2)e^(x)
e^x

```

```python

def expx(n):
    x = var("x")
    return exp(x**n)
[expx(2)*expx(0) - expx(1)]
```

    [-exp(x) + E*exp(x**2)]

x**2 + 1 = x

e^{x**2 + 1} = e^{x}

e{x**2} * e^{0} = e^{x}

y =

```python

ex = Function("ex", real=True, positive=True)
import functools


def lift(t):
    if t.is_Add:
        return sum(lift(c) for c in t.args)
    elif t.is_Mul:
        return functools.reduce(lambda a,b: a*b, (lift(c) for c in t.args))
    elif t.is_Function:
        return ex(t.args[0] + 1)
    elif t.is_Integer:
        return t
    else:
        raise ValueError("unknown term type", t)

def lift(t, d=1):
    n = Wild("n")
    return t.replace(ex(n), ex(n + d))

lift(ex(0)*ex(2) - ex(1))

def add_redundant(ts):
    res = ts.copy()
    for t in ts:
        res.append(lift(t))

def semigrob(ts,n=2):
    F = [Eq(lift(lhs,i), lift(rhs, i)) for lhs,rhs in ts for i in range(n+1)]
    gens = [ex(i) for i in reversed(range(2*n))]
    return groebner(F, *gens, order='lex')

def orient(eqs):
    oriented = []
    for eq in eqs:
        lhs, rhs = eq.args
        if lhs == rhs:
            continue
        lhs, rhs = abs(lhs), abs(rhs)
        if (lhs - rhs).LC() < 0:
            lhs, rhs = rhs, lhs
        oriented.append((lhs, rhs))
    return oriented

def translate(t):
    lhs, rhs = t.args
    lhs, rhs = abs(lhs), abs(rhs)
    n = Wild("n")
    x = var("x", positive=True, real=True)
    lhs = lhs.replace(ex(n), exp(x**n))
    rhs = rhs.replace(ex(n), exp(x**n))
    lhs,rhs = ln(lhs).simplify(), ln(rhs).simplify()
    if (lhs - rhs).LC() < 0:
        lhs, rhs = rhs, lhs
    return lhs,rhs

def untrans(lhs,rhs):
    n = Wild("n")
    x = var("x", positive=True, real=True)
    lhs = lhs.replace(x**n, ln(ex(n)))
    rhs = rhs.replace(x**n, ln(ex(n)))
    return lhs, rhs

G = semigrob([(ex(2)*ex(0),ex(1))], n=4)
for g in G:
    lhs,rhs = translate(g)
    #print(g)
    print(lhs, "=", rhs)






```

    ---------------------------------------------------------------------------

    AttributeError                            Traceback (most recent call last)

    Cell In[191], line 54
         52 G = semigrob([(ex(2)*ex(0),ex(1))], n=4)
         53 for g in G:
    ---> 54     lhs,rhs = translate(g)
         55     #print(g)
         56     print(lhs, "=", rhs)


    Cell In[191], line 41, in translate(t)
         39 rhs = rhs.replace(ex(n), exp(x**n))
         40 lhs,rhs = ln(lhs).simplify(), ln(rhs).simplify()
    ---> 41 if (lhs - rhs).LC() < 0:
         42     lhs, rhs = rhs, lhs
         43 return lhs,rhs


    AttributeError: 'Add' object has no attribute 'LC'

```python
ex = Function("ex", real=True, positive=True)
x = var("x", positive=True, real=True)
def abstract(t):
    n = Wild("n")
    return t.replace(x**n, ln(ex(n)))
exp(abstract(x**2 + 1)).simplify()
```

$\displaystyle \operatorname{ex}{\left(0 \right)} e^{\log{\left(\operatorname{ex}{\left(1 \right)} \right)}^{2}}$

softmax semiring? Boltzmann? Neural network? Hmm.
x circ y = ln(exp(x) + exp(y))

Brute equational search

t - lhs + rhs

def apply(t, lhs, rhs):
    n = t.degree_list()
    for i in range(n)
    t1 = t - lhs
    if all(c >= for c in t1.coeffs()):
        t1 + rhs

seen = {}
todo = queue()
while todo:
    t = todo.pop()
    for lhs,rhs in rules:
        for t1 in apply(t, lhs,rhs):
            if t1 in seen:
                continue
            else:
                todo.add(t1)
                seen[t1] = (t, rule)

```python
def rw(t, lhs, rhs):
    t,lhs,rhs = t.as_poly(), lhs.as_poly(), rhs.as_poly()
    n, = t.degree_list()
    divseq = []
    # reduction is non unique, even for single variable polynomials.
    # If I search matches in a different order, I may get a different result
    for i in reversed(range(n+1)): # x**n is the biggest monomial cofactor that could matter.
        while True:
            t1 = t - lhs * x**i
            if all(c >= 0 for c in t1.coeffs()):
                t = t1 + rhs * x**i
                divseq.append(x**i)
            else:
                break
    return t, divseq

rw(x**4 + x**2 + x, x**2 + 1, x)




```

    (Poly(x**2, x, domain='ZZ'), [x**2, x])

x = 1 + x^2
1 + x^2 = x
x + x^4 = 1 + x^3
x^5 = 1 + x^4
1 + x ^3 + x^n = x^n  3 <= n <= 4

```python
#srepr(x(0)*x(2) - x(1))
t = ex(0)*ex(2) - ex(1)
gens = [ex(n) for n in reversed(range(6))]
F = [t, lift(t), lift(lift(t))]
groebner(F, *gens, order="lex")

x = var("x")

def pseudo_log(t):
    lhs,rhs = t.args
    rhs = -1 * rhs
    lhs.args

```

```python
from sympy import *

sympy.var('p, n, d, q')
F = [p**5 - n, p**10 - d, p**25 - q]
G = groebner(F, order='grlex')
G
```

$\displaystyle \operatorname{GroebnerBasis}\left(\left( - n + p^{5}, \  d^{3} - n q, \  d^{2} n - q, \  - d + n^{2}\right), \left( p, \  q, \  d, \  n\right)\right)$

```python
import kdrag.solvers.kb.multiset as ms
ms.

```

```python
x = var("x")
((1 + x**2).as_poly(), x.as_poly())
type RigRewrite = tuple[sympy.Poly, sympy.Poly]

def pmatch(p, lhs) -> :
    n = 1
    while all(c >= 0 for c in (p - n * lhs).all_coeffs()):
        n += 1
    return n - 1

```

    (Poly(x**2 + 1, x, domain='ZZ'), Poly(x, x, domain='ZZ'))

```python
p = (1 + 2*x**2).as_poly()
p.all_terms()
divmod(p, x)
p.as_dict()

```

    {(0,): 1, (2,): 2}

```python
p.gens
```

    (x,)

```python
p.all_terms()
```

    [((2,), 2), ((1,), 0), ((0,), 1)]

```python

```

```python
def rw(x, lhs, rhs):
    y = x - lhs
    if all(y.coeffs() >= 0):
        return y + rhs
    else:
        return None

p = (x**2 + x**4).as_poly()

rw(p, x**2 + 1, x)
```

```python
p = 1 + x**2
def overlaps(p1, p2):
    res = []
    for c1 in p1.args:
        for c2 in p2.args:
            #print(c, c1, lcm(c,c1))
            l = lcm(c1, c2)
            q1,q2 = l / c1, l / c2
            t1, t2 = (q1 * p1, q2 * p2) # new critical pair
            gens = t1.as_poly().gens
            t1,t2 = t1.as_poly().as_dict(), t2.as_poly().as_dict()
            for k,v in t1.items():
                t2[k] = max(t2.get(k, 0), v)
            t2 = sympy.Poly.from_dict(t2, gens)
            res.append((t2,q1,q2))
    return res

overlaps(p,p)
            # max coeffs
def crits(rw1, rw2):
    lhs1, rhs1 = rw1
    lhs2, rhs2 = rw2
    res = []
    for (t,q1,q2) in overlaps(lhs1, lhs2):
        res.append((t + q1 * (rhs1 - lhs1), t + q2 * (rhs2 - lhs2)))
    return res
crits((1 + x**2, x), (1 + x**2, x))




```

    Poly(x**2 + 1, x, domain='ZZ') 1 1
    Poly(x**4 + x**2 + 1, x, domain='ZZ') x**2 1
    Poly(x**4 + x**2 + 1, x, domain='ZZ') 1 x**2
    Poly(x**2 + 1, x, domain='ZZ') 1 1





    [(Poly(x, x, domain='ZZ'), Poly(x, x, domain='ZZ')),
     (Poly(x**3 + 1, x, domain='ZZ'), Poly(x**4 + x, x, domain='ZZ')),
     (Poly(x**4 + x, x, domain='ZZ'), Poly(x**3 + 1, x, domain='ZZ')),
     (Poly(x, x, domain='ZZ'), Poly(x, x, domain='ZZ'))]

```python
def rw(t, lhs, rhs):
    t,lhs = t.as_poly(), lhs.as_poly()
    gens = t.gens
    lm = lhs.LM()
    t1 = t
    for m in t.all_monoms():
        if any(q < r for  q,r in zip(m, lm)):
            continue
        q = Monomial(m,gens) / lm
        while True:
            t2 = t1 - lhs * q.as_expr()
            if any(c < 0 for c in t2.all_coeffs()):
                break
            t1 = t2 + rhs * q.as_expr()
    return t1

rw(x**4 + x**2 + 3, x**2 + 1, x)
```

$\displaystyle \operatorname{Poly}{\left( x^{3} + 3, x, domain=\mathbb{Z} \right)}$

```python
from typing import NamedTuple


type Monom = tuple[int, ...]
type Poly = dict[Mono, int]
class Context(NamedTuple): # DivRem
    # rem + div * x
    div : Monom 
    rem : Poly
class Term(NamedTuple):
    coeff : int
    mono : Monom

def mono_lcm(m1,m2):
    return tuple(max(a,b) for a,b in zip(m1,m2))
def mono_div(m1, m2):
    return tuple(a - b for a,b in zip(m1,m2))
def mono_mul(m1, m2):
    return tuple(a + b for a,b in zip(m1,m2))
def mono_le(m1, m2):
    return all(a <= b for a,b in zip(m1,m2))

import math
math.lcm(4,5)

def poly_add(p1: Poly, p2: Poly) -> Poly:
    res = p1.copy()
    for m,c in p2.items():
        res[m] = res.get(m, 0) + c
    return res
def poly_sub(p1: Poly, p2: Poly) -> Poly:
    res = p1.copy()
    for m,c in p2.items():
        res[m] = res.get(m, 0) - c
    return res
def mono_mul_poly(m: Monom, c, int, p: Poly) -> Poly:
    return {mono_mul(m1, m): c*c1 for m1,c1 in p.items()}

def overlaps(p1: Poly, p2: Poly) -> list[tuple[Poly, Poly]]:
    res = []
    for m1,c1 in p1.items():
        for m2,c2 in p2.items():
            l,c3 = mono_lcm(m1, m2), math.lcm(c1, c2)
            q1, q2 = mono_div(l,m1), mono_div(l,m2)
            t1 = {mono_mul(m, q1): c * c3 // c1 for m,c in p1.items()}
            t2 = {mono_mul(m, q2): c * c3 // c2 for m ,c in p2.items()}
            for m,c in t2.items():
                t1[m] = max(t1.get(m, 0), c)
            res.append((t1, q1, q2))
    return res

def leading(p : Poly) -> tuple[Monom, int]:
    lm = max(p.keys())
    return lm, p[lm]

def poly_div(p: Poly, lhs: Poly) -> Context:
    lm = leading(lhs)
    div = {}
    rem = p.copy()
    for m,c in p.items():
        if mono_le(lm[0], m):
            q = mono_div(m, lm[0])
            


p = {(2, ) : 1, (0,): 1}
overlaps(p,p)
```

      Cell In[126], line 56
        p = {(2, ) : 1, (0,): 1}
                                ^
    IndentationError: expected an indented block after 'for' statement on line 54

```python
from typing import NamedTuple
class MonoXY(NamedTuple):
    x: int
    y: int
    def __mul__(self, other):
        return MonoXY(self.x + other.x, self.y + other.y)
    def __truediv__(self, other):
        return MonoXY(self.x - other.x, self.y - other.y)

def add(p1,p2):
    res = p1.copy()
    for m,c in p2.items():
        res[m] = res.get(m, 0) + c
    return res
def sub(p1,p2):
    res = p1.copy()
    for m,c in p2.items():
        res[m] = res.get(m, 0) - c
    return res
def mul(m1, p2):
    return {m1 * m: c*c1 for m,c1 in p2.items()}
def lm(p):
    return max(p.keys())
def lc(p):
    return p[lm(p)]
def lift(m):
    return {m: 1}


def divrem(p1, p2):
    div = {}
    rem = p1.copy()
    lm2 = lm(p2)
    lc2 = p2[lm2]
    while True:
        lm1 = lm(rem)
        lc1 = rem[lm1]
        if lc1 == 0:
            del rem[lm1]
            continue
        if lm1 < lm2:
            return div, rem
        m = lm1 / lm2
        c = rem[lm1] / lc2
        div = add(div, {m : c})
        rem = sub(rem, mul({m : c}, p2))

p1 = {MonoXY(4,0): 1, MonoXY(2,0): 1, MonoXY(0,0): 3}
p2 = {MonoXY(2,0): 1, MonoXY(0,0): 1}
divrem(p1, p2)


```

    ---------------------------------------------------------------------------

    TypeError                                 Traceback (most recent call last)

    Cell In[6], line 50
         48 p1 = {MonoXY(4,0): 1, MonoXY(2,0): 1, MonoXY(0,0): 3}
         49 p2 = {MonoXY(2,0): 1, MonoXY(0,0): 1}
    ---> 50 divrem(p1, p2)


    Cell In[6], line 46, in divrem(p1, p2)
         44 c = rem[lm1] / lc2
         45 div = add(div, {m : c})
    ---> 46 rem = sub(rem, mul({m : c}, p2))


    Cell In[6], line 21, in mul(m1, p2)
         20 def mul(m1, p2):
    ---> 21     return {m1 * m: c*c1 for m,c1 in p2.items()}


    TypeError: 'dict' object cannot be interpreted as an integer

```python

```

```python
def overlaps(p1, p2):
    terms1 = p1.all_terms()
    terms2 = p2.all_terms()
    res = []
    for (e1, c1) in terms1:
        if c1 == 0:
            continue
        for (e2, c2) in terms2:
            if c2 == 0:
                continue
        lcm()

```

```python
from sympy import Basic, sympify

class Opaque(Expr):
    def __new__(cls, data):
        obj = Basic.__new__(cls, sympify((str(data), data.get_id())))
        obj._payload = data
        return obj
    def _eval_is_integer(self):
        return self._payload.sort() == smt.IntSort()
    def _eval_is_integer(self):
        return self._payload.sort() == smt.IntSort() or self._payload.sort() == smt.RealSort()
    def _eval_evalf(self, prec):
        return self._payload
```

```python
from kdrag.all import *
z = smt.Int("z")
Opaque(z)
```

$\displaystyle \operatorname{Opaque}\left(\left( z, \  261\right)\right)$

```python

```

from kdrag.solver.kb

```python

```

# comlete code

AI. jesus.

```python
from dataclasses import dataclass, field
from collections import Counter
from typing import ClassVar, Optional


class MS(tuple):
    # multiset
    def __new__(cls, xs=()):
        return super().__new__(cls, sorted(xs))

    def __lt__(self, other):
        return (len(self), tuple(self)) < (len(other), tuple(other))


@dataclass
class Semi:
    outer_order: ClassVar[str] = "multilex"
    monoms: MS[MS[str]] = field(default_factory=MS)

    def __post_init__(self):
        self.monoms = MS(MS(m) for m in self.monoms)

    @staticmethod
    def lit(name) -> "Semi":
        return Semi([[name]])

    @staticmethod
    def of_int(n: int) -> "Semi":
        assert n >= 0
        if n == 0:
            return Semi([])
        elif n == 1:
            return Semi([[]])
        else:
            return Semi([[]]) + Semi.of_int(n - 1)

    def __add__(self, other: "Semi") -> "Semi":
        if isinstance(other, int):
            other = Semi.of_int(other)
        return Semi(MS((MS(self.monoms + other.monoms))))

    def __radd__(self, other: int) -> "Semi":
        return Semi.of_int(other) + self

    def __pow__(self, n: int) -> "Semi":
        assert n >= 0
        if n == 0:
            return Semi.of_int(1)
        result = self
        for _ in range(n - 1):
            result *= self
        return result

    def __mul__(self, other: "Semi") -> "Semi":
        return Semi(MS(MS(m1 + m2) for m1 in self.monoms for m2 in other.monoms))

    def __rmul__(self, other: int) -> "Semi":
        return Semi.of_int(other) * self

    def __repr__(self) -> str:
        return " + ".join([" ".join(m) if m else "1" for m in self.monoms])

    def __lt__(self, other: "Semi") -> bool:
        if Semi.outer_order == "multilex":
            return tuple(reversed(self.monoms)) < tuple(reversed(other.monoms))
        return self.monoms < other.monoms

    def __sub__(self, other: "Semi") -> Optional["Semi"]:
        res = list(self.monoms)
        for m in other.monoms:
            if m in res:
                res.remove(m)
            else:
                return None
        return Semi(MS(res))

    def divrem(self, other: "Semi") -> tuple["Semi", "Semi"]:
        # returns largest q such that self = q*other + r
        assert isinstance(other, Semi)
        if len(other.monoms) == 0:
            raise ValueError("division by zero")
        q = []
        r = self
        lm = other.monoms[-1]
        i = len(r.monoms) - 1
        while i >= 0:
            qm = list(r.monoms[i])
            for x in lm:
                if x not in qm:
                    break
                qm.remove(x)
            else:
                term = Semi([qm])
                r1 = r - term * other
                if r1 is not None:
                    q.append(MS(qm))
                    r = r1
                    i = len(r.monoms) - 1
                    continue
            i -= 1
        return Semi(q), r

    def overlaps(self, other) -> list["Semi"]:
        # return all nontrivial overlaps of self and other
        # such that ov = q1 * self + r1 and ov = q2 * other + r2
        # ov is less that lm(self) * lm(other) ?
        res = []
        for (q, r), _ in self.overlaps_qr(other):
            ov = q * self + r
            if ov not in res:
                res.append(ov)
        return res

    def overlaps_qr(
        self, other
    ) -> list[tuple[tuple["Semi", "Semi"], tuple["Semi", "Semi"]]]:
        # Polynomial contexts split additively, so align one monomial occurrence.
        res = []
        for m1 in Counter(self.monoms):
            for m2 in Counter(other.monoms):
                cm = Counter(m1) | Counter(m2)
                qm1 = MS((cm - Counter(m1)).elements())
                qm2 = MS((cm - Counter(m2)).elements())
                q1, q2 = Semi([qm1]), Semi([qm2])
                t1, t2 = q1 * self, q2 * other
                ov = Semi((Counter(t1.monoms) | Counter(t2.monoms)).elements())
                qr = ((q1, ov - t1), (q2, ov - t2))
                if qr not in res:
                    res.append(qr)
        return res


# hypothesis tests to check supposed properties


@dataclass(frozen=True, slots=True)
class Eq:  # It is itself a multiset
    lhs: Semi
    rhs: Semi


type Rewrites = list["Rewrite"]


def reduce(semi: Semi, rewrites: Rewrites) -> Semi:
    while True:
        for rw in rewrites:
            q, r = semi.divrem(rw.lhs)
            res = q * rw.rhs + r
            if res != semi:
                semi = res
                break
        else:
            return semi


@dataclass(slots=True)
class Rewrite:  # It is itself a multiset
    lhs: Semi
    rhs: Semi
    mark: bool = False

    def __init__(self, lhs: Semi, rhs: Semi, mark: bool = False):
        if lhs < rhs:
            lhs, rhs = rhs, lhs
        self.lhs, self.rhs, self.mark = lhs, rhs, mark

    def __str__(self) -> str:
        return f"{self.lhs} -> {self.rhs}"


def naive_complete(eqs: list[Eq]) -> list[Rewrite]:
    # naive completion algorithm
    pending = list(eqs)
    rws = []
    # in loop, reduce equations and add reduced oreitned form to rewrites
    while pending:
        eq = pending.pop(0)
        lhs, rhs = reduce(eq.lhs, rws), reduce(eq.rhs, rws)
        if lhs == rhs:
            continue
        rw = Rewrite(lhs, rhs)
        if rw in rws:
            continue
        # add all overlaps of rewrite lhs to equations
        rules = rws + [rw]
        for rw1 in rules:
            for (q, r), (q1, r1) in rw.lhs.overlaps_qr(rw1.lhs):
                lhs = reduce(q * rw.rhs + r, rules)
                rhs = reduce(q1 * rw1.rhs + r1, rules)
                eq = Eq(lhs, rhs)
                if lhs != rhs and eq not in pending:
                    pending.append(eq)
        rws.append(rw)
    return rws


def huet_complete(eqs: list[Eq]) -> list[Rewrite]:
    # huet completion algorithm without marking
    # similar to previous
    # keep equations
    E, R = list(eqs), []
    while True:
        # reduce lhs, rhs according to R
        while E:
            eq = E.pop()
            lhs, rhs = reduce(eq.lhs, R), reduce(eq.rhs, R)
            if lhs == rhs:
                continue
            rw = Rewrite(lhs, rhs)

            # collapse old left sides and compose old right sides
            R1 = [rw]
            for rw1 in R:
                lhs1 = reduce(rw1.lhs, [rw])
                if lhs1 == rw1.lhs:
                    rhs1 = reduce(rw1.rhs, R + [rw])
                    if rw1.lhs != rhs1:
                        R1.append(Rewrite(rw1.lhs, rhs1))
                else:
                    E.append(Eq(lhs1, rw1.rhs))
            R = R1

        # create all critical pairs; marking would avoid redoing old pairs
        for i, rw in enumerate(R):
            for rw1 in R[: i + 1]:
                for (q, r), (q1, r1) in rw.lhs.overlaps_qr(rw1.lhs):
                    lhs = reduce(q * rw.rhs + r, R)
                    rhs = reduce(q1 * rw1.rhs + r1, R)
                    eq = Eq(lhs, rhs)
                    if lhs != rhs and eq not in E:
                        E.append(eq)
        if not E:
            return R


def huet_marked(eqs: list[Eq]) -> list[Rewrite]:
    # the same as the above, but keep a bool in rewrite indicating if it is marked
    # the critical pair generation process picks one unwarked rules and generates critical pairs with all other rules, marking the rule after generating its critical pairs
    # if there are no unmarked rules, the algorithm terminates
    E, R = list(eqs), []
    while True:
        while E:
            eq = E.pop()
            lhs, rhs = reduce(eq.lhs, R), reduce(eq.rhs, R)
            if lhs == rhs:
                continue
            rw = Rewrite(lhs, rhs)

            R1 = [rw]
            for rw1 in R:
                lhs1 = reduce(rw1.lhs, [rw])
                if lhs1 == rw1.lhs:
                    rhs1 = reduce(rw1.rhs, R + [rw])
                    if rw1.lhs != rhs1:
                        R1.append(Rewrite(rw1.lhs, rhs1, rw1.mark))
                else:
                    E.append(Eq(lhs1, rw1.rhs))
            R = R1

        for rw in R:
            if not rw.mark:
                break
        else:
            return R

        rw.mark = True
        for rw1 in R:
            for (q, r), (q1, r1) in rw.lhs.overlaps_qr(rw1.lhs):
                lhs = reduce(q * rw.rhs + r, R)
                rhs = reduce(q1 * rw1.rhs + r1, R)
                eq = Eq(lhs, rhs)
                if lhs != rhs and eq not in E:
                    E.append(eq)

```

```python
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::fmt;
use std::time::Instant;

/// Graded lexicographic order used for monomials and polynomials.
fn lenlex<T: Ord>(xs: &[T], ys: &[T]) -> Ordering {
    xs.len().cmp(&ys.len()).then_with(|| xs.cmp(ys))
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Monom(Vec<u32>);

impl Ord for Monom {
    fn cmp(&self, other: &Self) -> Ordering {
        lenlex(&self.0, &other.0)
    }
}

impl PartialOrd for Monom {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Monom {
    /// Multiset union of variables.
    fn mul(&self, other: &Self) -> Self {
        let (mut i, mut j) = (0, 0);
        let mut out = Vec::with_capacity(self.0.len() + other.0.len());
        while i < self.0.len() && j < other.0.len() {
            if self.0[i] <= other.0[j] {
                out.push(self.0[i]);
                i += 1;
            } else {
                out.push(other.0[j]);
                j += 1;
            }
        }
        out.extend_from_slice(&self.0[i..]);
        out.extend_from_slice(&other.0[j..]);
        Self(out)
    }

    /// Remove `other` as a submultiset.
    fn div(&self, other: &Self) -> Option<Self> {
        let (mut i, mut j) = (0, 0);
        let mut out = Vec::with_capacity(self.0.len() - other.0.len().min(self.0.len()));
        while i < self.0.len() {
            if j < other.0.len() && self.0[i] == other.0[j] {
                i += 1;
                j += 1;
            } else if j < other.0.len() && self.0[i] > other.0[j] {
                return None;
            } else {
                out.push(self.0[i]);
                i += 1;
            }
        }
        (j == other.0.len()).then_some(Self(out))
    }

    /// Componentwise maximum of variable multiplicities.
    fn lcm(&self, other: &Self) -> Self {
        let (mut i, mut j) = (0, 0);
        let mut out = Vec::with_capacity(self.0.len() + other.0.len());
        while i < self.0.len() || j < other.0.len() {
            let x = match (self.0.get(i), other.0.get(j)) {
                (Some(&x), Some(&y)) => x.min(y),
                (Some(&x), None) => x,
                (None, Some(&y)) => y,
                (None, None) => unreachable!(),
            };
            let i0 = i;
            let j0 = j;
            while self.0.get(i) == Some(&x) {
                i += 1;
            }
            while other.0.get(j) == Some(&x) {
                j += 1;
            }
            out.extend(std::iter::repeat_n(x, (i - i0).max(j - j0)));
        }
        Self(out)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Semi(Vec<Monom>);

type QR = (Semi, Semi);
type Overlap = (QR, QR);

impl Ord for Semi {
    fn cmp(&self, other: &Self) -> Ordering {
        lenlex(&self.0, &other.0)
    }
}

impl PartialOrd for Semi {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Semi {
    /// Build a polynomial in canonical sorted form.
    fn new(mut monoms: Vec<Monom>) -> Self {
        monoms.sort_unstable();
        Self(monoms)
    }

    /// Embed a generator.
    fn lit(x: u32) -> Self {
        Self(vec![Monom(vec![x])])
    }

    /// Embed a natural number as repeated empty monomials.
    fn of_int(n: usize) -> Self {
        Self(vec![Monom(Vec::new()); n])
    }

    /// Merge the two sorted multisets of monomials.
    fn add(&self, other: &Self) -> Self {
        let (mut i, mut j) = (0, 0);
        let mut out = Vec::with_capacity(self.0.len() + other.0.len());
        while i < self.0.len() && j < other.0.len() {
            if self.0[i] <= other.0[j] {
                out.push(self.0[i].clone());
                i += 1;
            } else {
                out.push(other.0[j].clone());
                j += 1;
            }
        }
        out.extend_from_slice(&self.0[i..]);
        out.extend_from_slice(&other.0[j..]);
        Self(out)
    }

    /// Distributive product of every pair of monomials.
    fn mul(&self, other: &Self) -> Self {
        let mut out = Vec::with_capacity(self.0.len() * other.0.len());
        for m in &self.0 {
            for n in &other.0 {
                out.push(m.mul(n));
            }
        }
        Self::new(out)
    }

    /// Multiply by one monomial and a natural coefficient.
    fn shift_scale(&self, q: &Monom, coeff: usize) -> Self {
        let mut out = Vec::with_capacity(self.0.len() * coeff);
        for m in &self.0 {
            let mq = m.mul(q);
            out.extend(std::iter::repeat_n(mq, coeff));
        }
        Self::new(out)
    }

    /// Natural subtraction, failing if `other` is not contained.
    fn sub(&self, other: &Self) -> Option<Self> {
        let (mut i, mut j) = (0, 0);
        let mut out = Vec::with_capacity(self.0.len().saturating_sub(other.0.len()));
        while j < other.0.len() {
            while i < self.0.len() && self.0[i] < other.0[j] {
                out.push(self.0[i].clone());
                i += 1;
            }
            if i == self.0.len() || self.0[i] != other.0[j] {
                return None;
            }
            i += 1;
            j += 1;
        }
        out.extend_from_slice(&self.0[i..]);
        Some(Self(out))
    }

    /// Coefficientwise maximum of two polynomials.
    fn union_max(&self, other: &Self) -> Self {
        let (mut i, mut j) = (0, 0);
        let mut out = Vec::with_capacity(self.0.len().max(other.0.len()));
        while i < self.0.len() || j < other.0.len() {
            match (self.0.get(i), other.0.get(j)) {
                (Some(m), Some(n)) if m == n => {
                    let (i0, j0) = (i, j);
                    while self.0.get(i) == Some(m) {
                        i += 1;
                    }
                    while other.0.get(j) == Some(n) {
                        j += 1;
                    }
                    out.extend(std::iter::repeat_n(m.clone(), (i - i0).max(j - j0)));
                }
                (Some(m), Some(n)) if m < n => {
                    out.push(m.clone());
                    i += 1;
                }
                (Some(_), Some(n)) => {
                    out.push(n.clone());
                    j += 1;
                }
                (Some(m), None) => {
                    out.push(m.clone());
                    i += 1;
                }
                (None, Some(n)) => {
                    out.push(n.clone());
                    j += 1;
                }
                (None, None) => break,
            }
        }
        Self(out)
    }

    /// Greedily find `q, r` with `self = q * other + r`.
    fn divrem(&self, other: &Self) -> (Self, Self) {
        assert!(!other.0.is_empty(), "division by zero");
        let mut q = Vec::new();
        let mut r = self.clone();
        let lm = other.0.last().unwrap();
        let mut i = r.0.len();
        while i > 0 {
            let Some(qm) = r.0[i - 1].div(lm) else {
                i -= 1;
                continue;
            };
            let term = other.shift_scale(&qm, 1);
            if let Some(r1) = r.sub(&term) {
                q.push(qm);
                r = r1;
                i = r.0.len();
            } else {
                i -= 1;
            }
        }
        (Self::new(q), r)
    }

    /// Return both `(quotient, remainder)` views of each nontrivial overlap.
    fn overlaps_qr(&self, other: &Self) -> Vec<Overlap> {
        let mut res = Vec::new();
        let mut seen = Vec::new();
        let mut i = 0;
        while i < self.0.len() {
            let mut i1 = i + 1;
            while i1 < self.0.len() && self.0[i1] == self.0[i] {
                i1 += 1;
            }
            let c1 = i1 - i;
            let mut j = 0;
            while j < other.0.len() {
                let mut j1 = j + 1;
                while j1 < other.0.len() && other.0[j1] == other.0[j] {
                    j1 += 1;
                }
                let c2 = j1 - j;
                let cm = self.0[i].lcm(&other.0[j]);
                let qm1 = cm.div(&self.0[i]).unwrap();
                let qm2 = cm.div(&other.0[j]).unwrap();
                let c = lcm(c1, c2);
                let q1 = Self(vec![qm1.clone(); c / c1]);
                let q2 = Self(vec![qm2.clone(); c / c2]);
                let t1 = self.shift_scale(&qm1, c / c1);
                let t2 = other.shift_scale(&qm2, c / c2);
                let ov = t1.union_max(&t2);
                if !seen.contains(&ov) {
                    seen.push(ov.clone());
                    res.push(((q1, ov.sub(&t1).unwrap()), (q2, ov.sub(&t2).unwrap())));
                }
                j = j1;
            }
            i = i1;
        }
        res
    }
}

impl fmt::Display for Semi {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            return write!(f, "0");
        }
        let mut i = 0;
        while i < self.0.len() {
            if i != 0 {
                write!(f, " + ")?;
            }
            let mut i1 = i + 1;
            while i1 < self.0.len() && self.0[i1] == self.0[i] {
                i1 += 1;
            }
            if i1 - i != 1 {
                write!(f, "{}*", i1 - i)?;
            }
            let m = &self.0[i].0;
            if m.is_empty() {
                write!(f, "1")?;
            } else {
                let mut j = 0;
                while j < m.len() {
                    let mut j1 = j + 1;
                    while j1 < m.len() && m[j1] == m[j] {
                        j1 += 1;
                    }
                    let x = char::from_u32(u32::from(b'a') + m[j]).unwrap_or('?');
                    write!(f, "{x}")?;
                    if j1 - j != 1 {
                        write!(f, "^{}", j1 - j)?;
                    }
                    j = j1;
                }
            }
            i = i1;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Rule {
    lhs: Semi,
    rhs: Semi,
    marked: bool,
}

impl Rule {
    /// Orient an equation from larger to smaller.
    fn new(mut lhs: Semi, mut rhs: Semi) -> Self {
        if lhs < rhs {
            std::mem::swap(&mut lhs, &mut rhs);
        }
        Self {
            lhs,
            rhs,
            marked: false,
        }
    }
}

/// Reduce to normal form, optionally followed by some extra rules.
fn reduce_with(mut semi: Semi, rewrites: &[Rule], extra: &[Rule]) -> Semi {
    'again: loop {
        for rw in rewrites.iter().chain(extra) {
            let (q, r) = semi.divrem(&rw.lhs);
            let res = q.mul(&rw.rhs).add(&r);
            if res != semi {
                semi = res;
                continue 'again;
            }
        }
        return semi;
    }
}

fn reduce(semi: Semi, rewrites: &[Rule]) -> Semi {
    reduce_with(semi, rewrites, &[])
}

/// Normalize all critical pairs between two rules.
fn critical_pairs<'a>(
    rw: &'a Rule,
    rw1: &'a Rule,
    rules: &'a [Rule],
) -> impl Iterator<Item = Rule> + 'a {
    rw.lhs
        .overlaps_qr(&rw1.lhs)
        .into_iter()
        .filter_map(move |((q, r), (q1, r1))| {
            let lhs = reduce(q.mul(&rw.rhs).add(&r), rules);
            let rhs = reduce(q1.mul(&rw1.rhs).add(&r1), rules);
            (lhs != rhs).then(|| Rule::new(lhs, rhs))
        })
}

fn gcd(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn lcm(a: usize, b: usize) -> usize {
    a / gcd(a, b) * b
}

/// Basic completion with a FIFO equation queue.
fn naive_complete(eqs: Vec<Rule>) -> (Vec<Rule>, usize) {
    let mut pending: VecDeque<_> = eqs.into();
    let mut rws = Vec::new();
    let mut popped = 0;
    while let Some(eq) = pending.pop_front() {
        popped += 1;
        let lhs = reduce(eq.lhs, &rws);
        let rhs = reduce(eq.rhs, &rws);
        if lhs == rhs {
            continue;
        }
        let rw = Rule::new(lhs, rhs);
        if rws.contains(&rw) {
            continue;
        }
        let new = rws.len();
        rws.push(rw);
        for old in 0..=new {
            for eq in critical_pairs(&rws[new], &rws[old], &rws) {
                if !pending.contains(&eq) {
                    pending.push_back(eq);
                }
            }
        }
    }
    (rws, popped)
}

/// Huet completion: collapse left sides and compose right sides.
fn huet_complete(mut eqs: Vec<Rule>) -> Vec<Rule> {
    let mut rws = Vec::new();
    loop {
        while let Some(eq) = eqs.pop() {
            let lhs = reduce(eq.lhs, &rws);
            let rhs = reduce(eq.rhs, &rws);
            if lhs == rhs {
                continue;
            }
            let rw = Rule::new(lhs, rhs);

            let mut rws1 = vec![rw.clone()];
            for rw1 in &rws {
                let lhs1 = reduce(rw1.lhs.clone(), std::slice::from_ref(&rw));
                if lhs1 == rw1.lhs {
                    let rhs1 = reduce_with(rw1.rhs.clone(), &rws, std::slice::from_ref(&rw));
                    if rw1.lhs != rhs1 {
                        rws1.push(Rule::new(rw1.lhs.clone(), rhs1));
                    }
                } else {
                    eqs.push(Rule::new(lhs1, rw1.rhs.clone()));
                }
            }
            rws = rws1;
        }

        for i in 0..rws.len() {
            for j in 0..=i {
                for eq in critical_pairs(&rws[i], &rws[j], &rws) {
                    if !eqs.contains(&eq) {
                        eqs.push(eq);
                    }
                }
            }
        }
        if eqs.is_empty() {
            return rws;
        }
    }
}

/// Huet completion, pairing each rule only after it becomes unmarked.
fn huet_marked(mut eqs: Vec<Rule>) -> Vec<Rule> {
    let mut rws: Vec<Rule> = Vec::new();
    loop {
        while let Some(eq) = eqs.pop() {
            let lhs = reduce(eq.lhs, &rws);
            let rhs = reduce(eq.rhs, &rws);
            if lhs == rhs {
                continue;
            }
            let rw = Rule::new(lhs, rhs);

            let mut rws1 = vec![rw.clone()];
            for rw1 in &rws {
                let lhs1 = reduce(rw1.lhs.clone(), std::slice::from_ref(&rw));
                if lhs1 == rw1.lhs {
                    let rhs1 = reduce_with(rw1.rhs.clone(), &rws, std::slice::from_ref(&rw));
                    if rw1.lhs != rhs1 {
                        let mut rw2 = Rule::new(rw1.lhs.clone(), rhs1);
                        rw2.marked = rw1.marked;
                        rws1.push(rw2);
                    }
                } else {
                    eqs.push(Rule::new(lhs1, rw1.rhs.clone()));
                }
            }
            rws = rws1;
        }

        let Some(i) = rws.iter().position(|rw| !rw.marked) else {
            return rws;
        };
        let rw = rws[i].clone();
        rws[i].marked = true;

        for rw1 in &rws {
            for eq in critical_pairs(&rw, rw1, &rws) {
                if !eqs.contains(&eq) {
                    eqs.push(eq);
                }
            }
        }
    }
}

/// Assert Buchberger's criterion for the finished system.
fn check_complete(rules: &[Rule]) {
    for rw in rules {
        for rw1 in rules {
            assert!(critical_pairs(rw, rw1, rules).next().is_none());
        }
    }
}

fn main() {
    let a = Semi::lit(0);
    let one = Semi::of_int(1);
    let seed = Rule::new(one.add(&a.mul(&a)), a);

    let start = Instant::now();
    let (naive, popped) = naive_complete(vec![seed.clone()]);
    println!(
        "naive: {} rules, {popped} equations in {:?}",
        naive.len(),
        start.elapsed()
    );

    let start = Instant::now();
    let rules = huet_complete(vec![seed.clone()]);
    println!("Huet: {} rules in {:?}", rules.len(), start.elapsed());
    for rw in &rules {
        println!("{} -> {}", rw.lhs, rw.rhs);
    }

    let start = Instant::now();
    let marked = huet_marked(vec![seed]);
    println!(
        "Huet marked: {} rules in {:?}",
        marked.len(),
        start.elapsed()
    );

    let start = Instant::now();
    check_complete(&naive);
    check_complete(&rules);
    check_complete(&marked);
    println!("all systems complete ({:?})", start.elapsed());

    assert_eq!(Semi::of_int(0).add(&Semi::of_int(2)), Semi::of_int(2));
}

```
