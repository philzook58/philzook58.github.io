---
title: "Knuckledragger Analysis Etudes"
date: 2025-08-11
---

I got kind of discouraged maybe 6 months ago trying some real analysis stuff.

The following are some theorems about balls and contraction and distance functions. I'm not particularly proud of how annoying it was to prove some of these. I need to work on my attitude. I was in total distraught despair at every hiccup. That's no way to be.

The way the Knuckledragger backwards tactic system works is that you build intermediate goals and throw everything that would be needed to dignify the step into a bag. Then a big `qed` call at the end assembles the proof.

This worked nice in that it enabled one to break apart a big thing and figure out what was failing or give the existentials.

But sometimes the big qed wouldn't work which was super frustrating.

This could be because of bugs in my lemma recoding system, or just because it isn't obvious enough to z3 how to reassemble the proof from the bits (this should be pretty close to pure boolean reasoning, but if it unfolds or skolemizes or something before it realizes that, it's trouble).

So I've been moving to having tactics record a callback that applies a bolted on axiom schema for the particular move the tactic implements.

I've also made the bags of lemmas more scoped, so that z3 doesn't have as many things to look at.

Also, improvements to unfold using the new `FreshVar` axioms schema so that the trace doesn't record the full quantified definition axiom.

Still, doing higher order stuff in particular remains frustrating. Z3 is just not that good at higher order or very quantified reasoning.

Here I define open balls and what it means to be open. Using `<=` in the definition of `real_open` seems to be much easier than using `<` since I don't have to supply a point that is outside the ball but still in `A`. I hope that change is correct?

```python
from kdrag.all import *
import kdrag.theories.set as set_
import kdrag.theories.real as real
x,y,z = smt.Reals("x y z")

r = smt.Real("r")
def Ball(x,r):
    return smt.Lambda([y], real.abs(y - x) < r)
ball = kd.define("ball", [x, r], Ball(x, r))

RSet = set_.Set(smt.RealSort())
S = smt.Const("S", RSet)
real_open = kd.define(
        "real_open",
        [S],
        kd.QForAll([x], S[x], kd.QExists([r], r > 0, ball(x, r) <= S)),
    )



```

Some theorems come easy. The commented out ones not so much. They _should_ come easy since it's just (quantified) linarith reasoning + unfolding, not sure why they don't

```python


open_full = kd.prove(real_open(RSet.full), unfold=1)
open_empty = kd.prove(real_open(RSet.empty), unfold=1)
#open_pos = kd.prove(real_open(smt.Lambda([x], x > 0)), unfold=2)
#open_ball = kd.prove(real_open(ball(0,1)), unfold=3)
```

```python
x,r1,r2 = smt.Reals("x r1 r2")

ball_sub = kd.prove(kd.QForAll([x,r1,r2], r1 > 0, r2 > r1, ball(x, r1) <= ball(x, r2)), unfold=1)
#ball_empty = kd.prove(kd.QForAll([x,r], r <= 0, ball(x, 0) == RSet.empty), unfold=2)
```

All these messages are warnings in unfold because Z3 can't synthesize the total unfolding from the unfolding lemmas. I guess I have to make unfold an axiom. Using z3 `substitute_funs` ought to actually be kind of nice for this.

```python
l = kd.Lemma(kd.QForAll([x,r], r <= 0, ball(x, r) == RSet.empty))
x,r = l.fixes()
l.intros()
l.unfold()
l.unfold()
#l.ext()
l.auto()
#l.auto() # unreliable
ball_empty = l.qed()
ball_empty
```

    Admitting lemma (ball(x!546, r!547) == K(Real, False)) ==
    ((Lambda(y, absR(y - x!546) < r!547)) == K(Real, False))
    Admitting lemma ((Lambda(y, absR(y - x!546) < r!547)) == K(Real, False)) ==
    ((Lambda(y,
             If(y - x!546 >= 0, y - x!546, -(y - x!546)) < r!547)) ==
     K(Real, False))


    Something is off in unfold (ball(x!546, r!547) == K(Real, False)) ==
    ((Lambda(y, absR(y - x!546) < r!547)) == K(Real, False)) [|= ball(x!546, r!547) == (Lambda(y, absR(y - x!546) < r!547))]
    Something is off in unfold ((Lambda(y, absR(y - x!546) < r!547)) == K(Real, False)) ==
    ((Lambda(y,
             If(y - x!546 >= 0, y - x!546, -(y - x!546)) < r!547)) ==
     K(Real, False)) [|= ForAll(Y!552,
           absR(Y!552 - x!546) ==
           If(Y!552 - x!546 >= 0,
              Y!552 - x!546,
              -(Y!552 - x!546))), |= (Lambda(Y!552,
            If(Y!552 - x!546 >= 0,
               Y!552 - x!546,
               -(Y!552 - x!546)) <
            r!547)) ==
    (Lambda(y,
            If(y - x!546 >= 0, y - x!546, -(y - x!546)) < r!547))]

&#8870;ForAll([x!544, r!151],
       Implies(r!151 <= 0,
               ball(x!544, r!151) == K(Real, False)))

```python
l = kd.Lemma(smt.ForAll([x], ball(x, 0) == RSet.empty))
x = l.fix()
l.auto(by=[ball_empty(x, smt.RealVal(0))])
ball_rad0 = l.qed()
```

It is commonly the case, and I'm ok with, that z3 can't auto solve a goal because you need to peel it apart enough to give the existential term explicitly. I could add a metavariable facility to solve these variables via unification or `sympy.solve` (neither of these need to be in the trusted kernel for this purpose). Interesting avenue to persue.

More than once did I give the wrong thing to fill the existential and was mad at my system when in fact I was trying to prove a false goal. It would be nice to have better counterexample guardrails for this.

```python
l = kd.Lemma(real_open(ball(0,1)))
l.unfold()
x = l.fix()
l.intros()
l.exists(1-real.abs(x))
l.auto(unfold=2)
open_ball_unit = l.qed()
open_ball_unit
```

&#8870;real_open(ball(0, 1))

```python
l = kd.Lemma(real_open(smt.Lambda([x], x > 0)))
l.unfold()
x = l.fix()
l.intros()
l.exists(x/2)
l.split()
l.auto()
l.unfold(ball)
l.unfold(real.abs)
#l.auto()
l.lemmas[-1]
l.auto()
l.lemmas[-1]
l.qed()
#l.auto(unfold=2)
#l.auto(unfold=2)
#l.qed()
```

    Admitting lemma subset(ball(x!194, x!194/2), Lambda(x!174, x!174 > 0)) ==
    subset(Lambda(y, absR(y - x!194) < x!194/2),
           Lambda(x!174, x!174 > 0))
    Admitting lemma subset(Lambda(y, absR(y - x!194) < x!194/2),
           Lambda(x!174, x!174 > 0)) ==
    subset(Lambda(y,
                  If(y - x!194 >= 0, y - x!194, -(y - x!194)) <
                  x!194/2),
           Lambda(x!174, x!174 > 0))


    Something is off in unfold subset(ball(x!194, x!194/2), Lambda(x!174, x!174 > 0)) ==
    subset(Lambda(y, absR(y - x!194) < x!194/2),
           Lambda(x!174, x!174 > 0)) [|= ball(x!194, x!194/2) ==
    (Lambda(y, absR(y - x!194) < x!194/2))]
    Something is off in unfold subset(Lambda(y, absR(y - x!194) < x!194/2),
           Lambda(x!174, x!174 > 0)) ==
    subset(Lambda(y,
                  If(y - x!194 >= 0, y - x!194, -(y - x!194)) <
                  x!194/2),
           Lambda(x!174, x!174 > 0)) [|= ForAll(Y!201,
           absR(Y!201 - x!194) ==
           If(Y!201 - x!194 >= 0,
              Y!201 - x!194,
              -(Y!201 - x!194))), |= (Lambda(Y!201,
            If(Y!201 - x!194 >= 0,
               Y!201 - x!194,
               -(Y!201 - x!194)) <
            x!194/2)) ==
    (Lambda(y,
            If(y - x!194 >= 0, y - x!194, -(y - x!194)) <
            x!194/2))]

&#8870;real_open(Lambda(x!174, x!174 > 0))

I'm surprised how automatic this is.

```python
A,B = kd.FreshVars("A B", RSet)
l = kd.Lemma(smt.Implies(real_open(A) & real_open(B), real_open(A | B)))
l.unfold(real_open)
l.intros()
x = l.fix()
l.split(at=0)
l.instan(0, x)
l.instan(1, x)
l.auto()
open_union = l.qed().forall([A,B])
open_union
```

&#8870;ForAll([A!214, B!215],
       Implies(And(real_open(A!214), real_open(B!215)),
               real_open(union(A!214, B!215))))

```python
A,B = kd.FreshVars("A B", RSet)
l = kd.Lemma(smt.Implies(real_open(A) & real_open(B), real_open(A & B)))
l.unfold(real_open)
#l.unfold(ball)
#l.unfold(real.abs)
l.intros()
x = l.fix()
l.intros()
#r = l.fix()
l.split(at=0)
l.instan(0, x)
l.instan(1, x)
l.cases(A[x])
# A == False
l.cases(B[x])
l.auto() # impossible
l.auto()
# A == True
l.cases(B[x])
l.auto()
l.have(kd.QExists([r], r > 0, ball(x, r) <= B))
rB = l.einstan(-1)
l.have(kd.QExists([r], r > 0, ball(x, r) <= A))
rA = l.einstan(-1)
l.exists(real.min(rA, rB))
l.auto(unfold=1)
open_inter = l.qed().forall([A,B])
open_inter

```

&#8870;ForAll([A!233, B!234],
       Implies(And(real_open(A!233), real_open(B!234)),
               real_open(intersection(A!233, B!234))))

TODO: the bigunion of open sets ought to be open.

```python
import kdrag.theories.set as set_
RSet = set_.Set(smt.RealSort())
set_.bigunion(RSet)


```

bigunion

<https://en.wikipedia.org/wiki/Contraction_mapping>

Contraction mappings are really compelling to focus on. Theorems about contraction mappings are how you take rigorous numerics and turn them into theorems about actual fixed points.

Here is a definition of metric and theorem about it. It does seem like z3 is a little happier with me using FreshVar and quantifying afterwards rather than giving it the quantifier. Weird.

```python
x,y,z = kd.FreshVars("x y z", smt.RealSort())
dist = kd.define("dist", [x,y], real.abs(x - y))
dist.refl = kd.prove(kd.QForAll([x], dist(x, x) == 0), unfold=2)
dist.pos = kd.prove(kd.QForAll([x,y], x != y, dist(x, y) > 0), unfold=2)
dist.pos2 = kd.prove(kd.QForAll([x,y], dist(x, y) >= 0), unfold=2)
dist.sym = kd.prove(kd.QForAll([x,y], dist(x, y) == dist(y, x)), unfold=2)
#tri = kd.prove(kd.QForAll([x,y,z], smt.Abs(x - z) <= smt.Abs(x - y) + smt.Abs(y - z)))
dist.tri = kd.prove(dist(x, z) <= dist(x, y) + dist(y, z), unfold=2).forall([x,y,z])
a = kd.FreshVar("a", smt.RealSort())

```

```python
dist.linear = kd.prove(dist(a*x, a*y) == real.abs(a)*dist(x,y), unfold=2).forall([a,x,y])
```

```python
RFun = smt.ArraySort(smt.RealSort(), smt.RealSort())
S = smt.Const("S", RSet)
f = smt.Const("f", RFun)
q = smt.Real("q")
contractive = kd.define("contract", [S, f], kd.QExists([q], q >= 0, q < 1, kd.QForAll([x,y], S[x], S[y], dist(f[x], f[y]) <= q*dist(x, y))))
```

```python
l = kd.Lemma(contractive(RSet.full, smt.Lambda([x], x/2)))
l.unfold(contractive)
l.exists(1/smt.RealVal(2))
l.split()
l.auto()
l.auto()
x,y = l.fixes()
l.intros()
l.simp()
#l.rw(dist.linear(1/smt.RealVal(2), x, y))
l.have(smt.simplify(dist(x/2, y/2)) == 1/2*dist(x,y), by=[dist.linear(1/smt.RealVal(2), x, y), real.abs.defn(1/smt.RealVal(2))])
l.auto()
l.qed()
#l.auto(by=[dist.pos2(x,y)])
#l.auto(by=[dist.linear(1/smt.RealVal(2), x, y), dist.pos2(x,y), real.abs.defn(1/smt.RealVal(2))], unfold=3)
```

&#8870;contract(K(Real, True), Lambda(x!470, x!470/2))

```python
l = kd.Lemma(contractive(RSet.full, smt.Lambda([x], x/2)))
x0 = x
l.unfold(contractive)
l.exists(1/smt.RealVal(2))
l.split()
l.auto()
l.auto()
x,y = l.fixes()
l.auto(by=[dist.linear(1/smt.RealVal(2), x, y), real.abs.defn(1/smt.RealVal(2))])
l.qed()
```

&#8870;contract(K(Real, True), Lambda(x!541, x!541/2))

```python
cont = kd.define("cont", [S, f], kd.QForAll([A], A <= S, open_real(A), open_real(set_.InvImage(f, A))))
```

Something I kind of have been liking the idea of is using python `Protocol` as my abstraction layer. They aren't part of the trusted kernel, they just organize concepts. I want to lie cleanly in python idioms.

```python
from kdrag.all import *
from typing import Protocol, runtime_checkable

@runtime_checkable
class MetricSpace(Protocol):
    M : smt.ArrayRef
    dist : smt.FuncDeclRef
    refl : kd.Proof
    pos : kd.Proof
    symm : kd.Proof
    tri : kd.Proof

x,y,z = smt.Reals("x y z")
# Slightly odd usage of class. Don't instantiate. Everything is class member
# It's really just a fancy dict.
class MetricR:
    M = smt.RealSort()
    dist = smt.Lambda([x,y], smt.Abs(x - y))
    refl = kd.prove(smt.ForAll([x], dist(x, x) == 0))
    pos = kd.prove(smt.ForAll([x, y], dist(x, y) >= 0))
    symm = kd.prove(smt.ForAll([x, y], dist(x, y) == dist(y, x)))
    tri = kd.prove(smt.ForAll([x,y,z] , dist(x, z) <= dist(x, y) + dist(y, z)))
assert isinstance(MetricR, MetricSpace)
```

# Bits and Bobbles

This whole post was bits and bobbles really.

I should supposedly be using a filter approach. It seems like everyone does that  <https://link.springer.com/chapter/10.1007/978-3-642-39634-2_21>

Writing down these definitions is painful.

Figuring out analysis, my system, and how to formalize all at the same time is very painful.

```python
def unfold(e: smt.ExprRef, defn_eqs: Sequence[kd.Proof]):
    """
    Unfold a definitional equation. The order of variables is off from what kd.define returns.

    >>> x = smt.Int("x")
    >>> y = smt.Real("y")
    >>> f = smt.Function("test_f", smt.IntSort(), smt.RealSort(), smt.RealSort())
    >>> defn = kd.axiom(smt.ForAll([y,x], f(x,y) == (x + 2*y)))
    >>> unfold(f(7,8), [defn])
    |= test_f(7, 8) == ToReal(7) + 2*8
    """
    assert all(isinstance(pf, kd.Proof) for pf in defn_eqs)
    subst = []
    for pf in defn_eqs:
        thm = pf.thm
        if isinstance(thm, smt.QuantifierRef) and thm.is_forall():
            eq = thm.body()
            lhs, rhs = eq.arg(0), eq.arg(1)
            decl = lhs.decl()
            arity = decl.arity()
            for n, v in enumerate(lhs.children()):
                assert smt.is_var(v) and smt.get_var_index(v) == n
            subst.append((decl, rhs))
        elif smt.is_eq(thm):
            lhs, rhs = thm.arg(0), thm.arg(1)
            assert smt.is_const(lhs)
            decl = lhs.decl()
            subst.append((decl, rhs))
        else:
            raise ValueError("Unfolding only works for definitional equalities", pf)
    return kd.axiom(e == smt.substitute_funs(e, *subst), by=["unfold", defn_eqs])
```

```python
f = smt.Lambda([x0], x0/2)
S = RSet.full
print(contractive(S,f))
print(kd.QExists([q], q >= 0, q < 1, kd.QForAll([x,y], S[x], S[y], dist(f[x], f[y]) <= q*dist(x, y))))
```

    contract(K(Real, True), Lambda(x!541, x!541/2))
    Exists(q,
           And(q >= 0,
               q < 1,
               ForAll([x!544, y!545],
                      Implies(And(K(Real, True)[x!544],
                                  K(Real, True)[y!545]),
                              dist(Lambda(x!541, x!541/2)[x!544],
                                   Lambda(x!541, x!541/2)[y!545]) <=
                              q*dist(x!544, y!545)))))

```python
(contractive(S,f) == kd.QExists([q], q >= 0, q < 1, kd.QForAll([x,y], S[x], S[y], dist(f[x], f[y]) <= q*dist(x, y)))).get_id()
```

    2230

```python
s = smt.Solver()
b = smt.Bool("b")
f = smt.Lambda([x], x/2)
S = RSet.full
s.add(contractive(S,f) == kd.QExists([q], q >= 0, q < 1, kd.QForAll([x,y], S[x], S[y], dist(f[x], f[y]) <= q*dist(x, y))))
s.add(smt.Not(contractive(S,f) == kd.QExists([q], q >= 0, q < 1, kd.QForAll([x,y], S[x], S[y], dist(f[x], f[y]) <= q*dist(x, y)))))
s.check()
```

<b>unsat</b>

```python

```

Slotted hash cons
Lean as simplifier
prob pl
asm v erify 3
quickchecking dependent types
