---
title: "State of Knuckledragger III: Kernel Changes, Symbolic Union, AI, and more"
date: 2026-03-02
---


Maybe a good idea to take stock of how Knuckledragger <https://github.com/philzook58/knuckledragger> is going for myself and whomever might be interested.

Some highlights from the last six months:

- Kernel Changes
- Experiments using AI
- Improved vampire smtlib support via lambda lifting
- Symbolic Union
- microlean syntax <https://www.philipzucker.com/kd_microlean/> is wired up pretty much everywhere. I don't tend to use it
- Towards External Proof objects
- Assembly verification <https://www.philipzucker.com/asm_verify4/>
- Defocus from generics
- Defocus from what others want to what I want
- ZFC experiments <https://www.philipzucker.com/zf_knuckle1/>
- Analysis Experiments  <https://github.com/philzook58/knuckledragger/tree/main/src/kdrag/theories/real>
- Moved more commonly used functionality up to top level `kdrag`
- Switched to ty typechecking. So fast, so good.

Top of the mind:

- External proof objects and external checkers
- Extracting smtlib benchmarks. I can scan python memory and emit smt scripts of all proof steps
- Enabling more cvc5 and vampire
- Everything is too verbose.
- Actual termination checking of definitions
- Inductive relations. Define least fixed point, derive the appropriate lemmas. The honest way of doing it like explained <https://isabelle.in.tum.de/website-Isabelle2011-1/dist/Isabelle2011-1/doc/ind-defs.pdf>
- Just doing fun knuth bendix / superposition stuff
- Proof by saturation / consistency / confluence
- Embedding Scryer Prolog <https://pypi.org/project/kdrag-scryer/> and Steel Scheme as helper libraries / DSLs. LeanTAP like provers, typeclass like search, minikanren. Or janus-swi

# Kernel Changes

The core of knuckledragger is that in principle you state some axioms and you have a single proof rule "super modus" that uses an ATP to determined you can derive P from P1,P2,...

```
|= P1   |= P2 ...     Not(Implies(And(P1,P2,...),P))    unsat
----------------------------
       |= P
```

I always knew that z3 was not a complete semi decision procedure for first order logic, but when it comes to quantifiers, sometimes I couldn't get what I considered a single step of quantifier manipulation to go through.

It is fantastic how fast z3 is per query. If we're running many many queries, it is not desirble for even 0.1s of start up time for a solver. Z3 often can dicharge even quite gnarly goals, you just can't count on it and need a fallback.

Two built in kernel rules are for herbrandization and skolemization. Skolemization lets you give a name the the thing an existential guarantees exsists. Herbrandization makes a generic fresh constant you know nothing about. If you can prove something about it, it is true for all things. Both of these currently have the character of gensyms, which is fine but a bit ugly especially when it comes to proof certificates. Their order of generation can matter.

But really this isn't enough. You do need to assert axioms, and some seem so fundamental that they are basically part of the kernel as well. It is a judgement call what moves in and out of the kernel.

I have moved the induction principle generator for algebraic datatypes into the kernel. I could also possibly move the induction principle for Int into the kernel.

A new mechanism is that of declaring constants, reserving the name for you explicit use.

A problem I've had is that the programmatic z3 api allows sort based overloading of names, but serializing these out into smtlib or tptp does not. So a somewhat harsh but familiar condition from module-less systems like C is to just require all names be distinct and make any clash an error. This simplifies many things and is basically doable.

Currently definitions have the force of axioms. The onus of their consistency is on you. I like this because sometimes I want to be nannyied but sometimes I don't. But I have felt I would like a little more

# Experiments in AI

AI is all the rage. I mostly use Codex because that is what I have a subscription for. The local agentic things that have access to your CLI are light years better than anything else.

AI is very very good at using knuckledragger out of the box. They can grep through the code base and get the gist. Also the knuckledragger tactics system is modelled closely after Lean or Rocq's in tactic names etc, just with a python facelift.

Knuckledragger is not uniquely good at being used by AI. AI is also very good at using Lean , Isabelle, etc. It's insane.

I was pushed to try this more by this paper <https://arxiv.org/abs/2601.03298>  "130k Lines of Formal Topology in Two Weeks: Simple and Cheap Autoformalization for Everyone? - Josef Urban" Josef is the real deal.

And yet, it also sucks a little bit. It can just worm around writing a bunch of mostly useless theorems and occasionally just not actually finish out proofs, write axioms, etc. One of the most insidious things it can do is strengthen preconditions or definitions until your theorem becomes true. This _is_ a part of theorem proving, an important part. Realizing the preconditions that you actually need. But if taken too far, either 1. your preconditions become false 2. your theorem becomes too close to the preconditions to be interesting. Again, 2. kind of _is_ the game of elegant mathematics, but you need taste. Neither of these are inconsistencies in anything, but they mean the system does not prove what you think it does

Another issue is that as it blasts out mountains of code, I can't keep up. And then when I see the final theorem statement, I don't even know what it means really. This is also the experience my manager experiences with me, so it is a window of empathy. Ultimately, the value of the proofs is more trust in me than it is direct trust in my proofs or theorem statements. It was also always possible to mis-model a system and no proof assistant can fix that.

I have tried giving AI

- Software foundations
- Real Analysis Game - I got around 12 chapters in. It's really nice for me how monomorphic they approached analysis to just work on R.
- Isabelle's Concrete Semantics

And tried to get it o translate these to knuckledragger by making a folder that has the git clone of these repos, git clone of knuckledragger, and a venv set up. It's been interesting and useful. Mostly it can slam through them, but as I watch I realize that this or that tactic isn't working right.

In terms of developing knuckledragger itself, AI has not been that useful. I need or want to keep a handle on the codebase and I don't want it filled with verbose junk.

I have been using it to develop lark grammars for TPTP, SMTLIB, and TLA syntax with mixed results. At first I am blown away.
I could get data sets of these formats and hopefully round trip them and hypothesis check them. These are quite concrete tasks. I was inspired by <https://simonwillison.net/2025/Dec/15/porting-justhtml/> where ai can do incredible things porting or developing parsers. Parsers are a lot of bulk, mostly mundane work.

Having said that, I don't know after the absolute shock of the initial product if it is good enough to be useful.

I have also used AI to help me write initial Maturin bindings to useful rust projects. It does a great job getting this started, but I think ultimately the best thing is for me to start a second project and copy over the things I like piece by piece.

I dunno. I am totally freaked out by AI every other day. But in sum total, it is kind of a wash, maybe a slight boost. You have to count all the time I'm waiting around or thinking about AI when I could be thinking about something else. Also the stress is causes me.

This Knaster Tarski theorem was one shotted by AI given access to the knuckledragger repo. This was quite impressive to me.

I also added knuckledragger to PyPI and lowered the requirements to python 3.11, because then the stock chatgpt web client could download and use it. That was cool, but ultimately it wasn't that good at using it compared to the local agents.

<https://github.com/philzook58/knuckledragger/blob/main/examples/kt.py>

```python
import kdrag as kd
import kdrag.smt as smt

# Declare an abstract complete lattice
L = smt.DeclareSort("L")
SetL = smt.SetSort(L)

x, y, z = smt.Consts("x y z", L)
A, B = smt.Consts("A B", SetL)

le = smt.Function("le", L, L, smt.BoolSort())
kd.notation.le.register(L, le)

le_refl = kd.axiom(smt.ForAll([x], x <= x))
le_trans = kd.axiom(smt.ForAll([x, y, z], smt.Implies(smt.And(x <= y, y <= z), x <= z)))
le_antisym = kd.axiom(smt.ForAll([x, y], smt.Implies(smt.And(x <= y, y <= x), x == y)))

is_ub = kd.define("is_ub", [A, y], kd.QForAll([x], A[x], x <= y))
is_lb = kd.define("is_lb", [A, y], kd.QForAll([x], A[x], y <= x))

sup = smt.Function("sup", SetL, L)
inf = smt.Function("inf", SetL, L)

sup_is_ub = kd.axiom(smt.ForAll([A], is_ub(A, sup(A))))
sup_least = kd.axiom(smt.ForAll([A, y], smt.Implies(is_ub(A, y), sup(A) <= y)))

inf_is_lb = kd.axiom(smt.ForAll([A], is_lb(A, inf(A))))
inf_greatest = kd.axiom(smt.ForAll([A, y], smt.Implies(is_lb(A, y), y <= inf(A))))

# Monotone functions on L (represented as arrays L -> L)
FSort = smt.ArraySort(L, L)
f = smt.Const("f", FSort)

monotone = kd.define(
    "monotone", [f], smt.ForAll([x, y], smt.Implies(x <= y, f[x] <= f[y]))
)

prefixed = kd.define("prefixed", [f], smt.Lambda([x], f[x] <= x))
postfixed = kd.define("postfixed", [f], smt.Lambda([x], x <= f[x]))

lfp = kd.define("lfp", [f], inf(prefixed(f)))
gfp = kd.define("gfp", [f], sup(postfixed(f)))

prefixed_eval = kd.prove(
    smt.ForAll([f, x], prefixed(f)[x] == (f[x] <= x)), by=[prefixed.defn]
)
postfixed_eval = kd.prove(
    smt.ForAll([f, x], postfixed(f)[x] == (x <= f[x])), by=[postfixed.defn]
)


@kd.Theorem(smt.ForAll([f], smt.Implies(monotone(f), f[lfp(f)] <= lfp(f))))
def lfp_prefixed(l):
    f = l.fix()
    l.intros()
    l.unfold(lfp)
    P = prefixed(f)

    l.apply(inf_greatest)
    l.unfold(is_lb)
    x = l.fix()
    l.intros()

    l.have(is_lb(P, inf(P)), by=[inf_is_lb(P)])
    l.unfold(is_lb, at=-1)
    l.specialize(-1, x)
    l.have(inf(P) <= x, by=[])

    l.unfold(monotone, at=0)
    l.specialize(0, inf(P), x)
    l.have(f[inf(P)] <= f[x], by=[])

    l.have(f[x] <= x, by=[prefixed_eval])
    l.auto(by=[le_trans])


@kd.Theorem(smt.ForAll([f], smt.Implies(monotone(f), lfp(f) <= f[lfp(f)])))
def lfp_postfixed(l):
    f = l.fix()
    l.intros()
    l.unfold(lfp)
    P = prefixed(f)

    l.have(f[lfp(f)] <= lfp(f), by=[lfp_prefixed(f)])
    l.unfold(lfp, at=-1)

    l.unfold(monotone, at=0)
    l.specialize(0, f[inf(P)], inf(P))
    l.have(f[f[inf(P)]] <= f[inf(P)], by=[])

    l.have(prefixed(f)[f[inf(P)]], by=[prefixed_eval])

    l.have(is_lb(P, inf(P)), by=[inf_is_lb(P)])
    l.unfold(is_lb, at=-1)
    l.specialize(-1, f[inf(P)])
    l.have(inf(P) <= f[inf(P)], by=[])
    l.auto()


@kd.Theorem(smt.ForAll([f], smt.Implies(monotone(f), f[lfp(f)] == lfp(f))))
def lfp_fixed(l):
    f = l.fix()
    l.intros()
    l.apply(le_antisym)
    l.have(f[lfp(f)] <= lfp(f), by=[lfp_prefixed(f)])
    l.have(lfp(f) <= f[lfp(f)], by=[lfp_postfixed(f)])
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [f, x],
        smt.Implies(smt.And(monotone(f), f[x] == x), lfp(f) <= x),
    )
)
def lfp_least(l):
    f, x = l.fixes()
    l.intros()
    l.unfold(lfp)
    P = prefixed(f)

    l.have(prefixed(f)[x], by=[prefixed_eval, le_refl])

    l.have(is_lb(P, inf(P)), by=[inf_is_lb(P)])
    l.unfold(is_lb, at=-1)
    l.specialize(-1, x)
    l.have(inf(P) <= x, by=[])
    l.auto()


@kd.Theorem(smt.ForAll([f], smt.Implies(monotone(f), gfp(f) <= f[gfp(f)])))
def gfp_postfixed(l):
    f = l.fix()
    l.intros()
    l.unfold(gfp)
    Q = postfixed(f)

    l.apply(sup_least)
    l.unfold(is_ub)
    x = l.fix()
    l.intros()

    l.have(is_ub(Q, sup(Q)), by=[sup_is_ub(Q)])
    l.unfold(is_ub, at=-1)
    l.specialize(-1, x)
    l.have(x <= sup(Q), by=[])

    l.unfold(monotone, at=0)
    l.specialize(0, x, sup(Q))
    l.have(f[x] <= f[sup(Q)], by=[])

    l.have(x <= f[x], by=[postfixed_eval])
    l.auto(by=[le_trans])


@kd.Theorem(smt.ForAll([f], smt.Implies(monotone(f), f[gfp(f)] <= gfp(f))))
def gfp_prefixed(l):
    f = l.fix()
    l.intros()
    l.unfold(gfp)
    Q = postfixed(f)

    l.have(gfp(f) <= f[gfp(f)], by=[gfp_postfixed(f)])
    l.unfold(gfp, at=-1)

    l.unfold(monotone, at=0)
    l.specialize(0, sup(Q), f[sup(Q)])
    l.have(f[sup(Q)] <= f[f[sup(Q)]], by=[])

    l.have(postfixed(f)[f[sup(Q)]], by=[postfixed_eval])
    l.have(is_ub(Q, sup(Q)), by=[sup_is_ub(Q)])
    l.unfold(is_ub, at=-1)
    l.specialize(-1, f[sup(Q)])
    l.have(f[sup(Q)] <= sup(Q), by=[])
    l.auto()


@kd.Theorem(smt.ForAll([f], smt.Implies(monotone(f), f[gfp(f)] == gfp(f))))
def gfp_fixed(l):
    f = l.fix()
    l.intros()
    l.apply(le_antisym)
    l.have(f[gfp(f)] <= gfp(f), by=[gfp_prefixed(f)])
    l.have(gfp(f) <= f[gfp(f)], by=[gfp_postfixed(f)])
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [f, x],
        smt.Implies(smt.And(monotone(f), f[x] == x), x <= gfp(f)),
    )
)
def gfp_greatest(l):
    f, x = l.fixes()
    l.intros()
    l.unfold(gfp)
    Q = postfixed(f)

    l.have(postfixed(f)[x], by=[postfixed_eval, le_refl])

    l.have(is_ub(Q, sup(Q)), by=[sup_is_ub(Q)])
    l.unfold(is_ub, at=-1)
    l.specialize(-1, x)
    l.have(x <= sup(Q), by=[])
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [f],
        smt.Implies(
            monotone(f),
            smt.And(
                f[lfp(f)] == lfp(f),
                f[gfp(f)] == gfp(f),
                kd.QForAll([x], f[x] == x, lfp(f) <= x),
                kd.QForAll([x], f[x] == x, x <= gfp(f)),
            ),
        ),
    )
)
def knaster_tarski(l):
    f = l.fix()
    l.intros()
    l.have(f[lfp(f)] == lfp(f), by=[lfp_fixed(f)])
    l.have(f[gfp(f)] == gfp(f), by=[gfp_fixed(f)])
    l.have(
        kd.QForAll([x], f[x] == x, lfp(f) <= x),
        by=[lfp_least],
    )
    l.have(
        kd.QForAll([x], f[x] == x, x <= gfp(f)),
        by=[gfp_greatest],
    )
    l.auto()
```

# lambda lifting

Vampire does support SMTLIB. Ultimately, I think this is easier than me outputting TPTP but I also can do that. It's just a little buggy.

An essential feature that the provers don't agree on is lambda. I have ended up using it a lot because z3 supports it and it is really useful to have lambdas.

I built a lambda lifting routine (and currying. Z3 supports multi-arity lambdas/Array and the other systems don't)

<https://github.com/philzook58/knuckledragger/blob/53e4628dd8ee7c72ef0258e2746d8e8b19c38fad/src/kdrag/utils.py#L475>

```python
def lambda_lift(expr: smt.ExprRef) -> tuple[smt.ExprRef, list[smt.BoolRef]]:
    """
    Traverses expression and lifts out lambdas to fresh top level functions.
    https://en.wikipedia.org/wiki/Lambda_lifting

    >>> x,y,z = smt.Ints("x y z")
    >>> lambda_lift(smt.ForAll([x,y], smt.Exists([z], x + y + 1 == smt.Lambda([z], x)[z])))
    (ForAll([x, y], Exists(z, x + y + 1 == f!...(x, y)[z])), [ForAll([x, y, z], f!...(x, y)[z] == x)])
    """
    lift_defs: list[smt.BoolRef] = []

    def worker(expr, env):
        if isinstance(expr, smt.QuantifierRef):
            vs, body = kd.utils.open_binder_unhygienic(expr)
            env = [v for v in env if not any(v.eq(v1) for v1 in vs)]  # shadowing
            env1 = env + vs
            if expr.is_lambda():
                f = smt.FreshFunction(*[v.sort() for v in env], expr.sort())
                lift_defs.append(smt.ForAll(env1, f(*env)(*vs) == worker(body, env1)))
                return f(*env)
            elif expr.is_forall():
                return smt.ForAll(vs, worker(body, env1))
            elif expr.is_exists():
                return smt.Exists(vs, worker(body, env1))
            else:
                raise NotImplementedError("Unknown quantifier type", expr)
        elif smt.is_const(expr):
            return expr
        elif smt.is_app(expr):
            args = [worker(arg, env) for arg in expr.children()]
            return expr.decl()(*args)
        else:
            raise Exception("Unexpected term in lambda_lift", expr)

    env = []
    return worker(expr, env), lift_defs


def curry_arrays(e: smt.ExprRef) -> smt.ExprRef:
    """
    Curry all selects and lambdas into single argument versions.
    >>> f = smt.Array("f", smt.IntSort(), smt.RealSort(), smt.BoolSort())
    >>> curry_arrays(smt.Select(f, smt.IntVal(3), smt.RealVal(2.0)))
    f[3][2]
    >>> x,y,z = smt.Ints("x y z")
    >>> curry_arrays(smt.Lambda([x,y], x + y)[2,3])
    Lambda(x, Lambda(y, x + y))[2][3]
    """
    # TODO  Possibility of clashing names here.
    # If you have the same name for the curried version you're nuts though.
    if isinstance(e, smt.QuantifierRef):
        vs, body = open_binder_unhygienic(e)
        body = curry_arrays(body)
        if e.is_lambda():
            for v in reversed(vs):
                body = smt.Lambda([v], body)
            return body
        elif e.is_forall():
            return smt.ForAll(vs, body)
        elif e.is_exists():
            return smt.Exists(vs, body)
        else:
            raise NotImplementedError("Unknown quantifier type", e)
    elif smt.is_const(e):
        if isinstance(e, smt.ArrayRef):
            doms = smt.domains(e)
            if len(doms) == 1:
                return e
            else:
                sort = e.range()
                for d in reversed(doms):
                    sort = smt.ArraySort(d, sort)
                return smt.Const(e.decl().name(), sort)
        else:
            return e
    elif smt.is_app(e):
        f, children = e.decl(), e.children()
        children = [curry_arrays(c) for c in children]
        if smt.is_select(e):
            arr = children[0]
            for index in children[1:]:
                arr = smt.Select(arr, index)
            return arr
        else:
            return f(*children)
    else:
        raise Exception("Unexpected term in curry_arrays", e)


```

# Symbolic Union

I was excited to develop a symbolic union type a la Rosette, but when I went to plug it in, I wasn't so sure it's useful.

Symbolic unions are a reification of symbolic executor state. Basically they a taking path conditions and values an packaging them up into a data structure

<https://docs.racket-lang.org/rosette-guide/sec_value-reflection.html>
<https://hackage.haskell.org/package/grisette>

I'm intrigued by what python t-strings in 3.14 might enable.

I could go the direction of verifying pseudo python. I just don't find it that interesting? I dunno. If someone could use such a thing, that could change the calculus.

```python

from dataclasses import dataclass
import kdrag.smt as smt
from typing import Callable, Optional
import operator
from functools import singledispatch
import kdrag as kd


@dataclass(frozen=True)
class SymUnion[T]:
    """
    Symbolic Union. A SymUnion[T] represents a value of type T that can be one of several possibilities,
    each with an associated symbolic boolean condition.

    https://docs.racket-lang.org/rosette-guide/sec_value-reflection.html
    https://hackage.haskell.org/package/grisette

    >>> su1 = SymUnion.wrap(42)

    """

    values: tuple[tuple[smt.BoolRef, T], ...]

    @classmethod
    def of_list(cls, values: list[tuple[smt.BoolRef, T]]) -> "SymUnion[T]":
        """
        Create a SymUnion from a list of (condition, value) pairs.

        >>> su2 = SymUnion.of_list([(smt.BoolVal(True), 42), (smt.BoolVal(False), 43)])
        >>> su2
        SymUnion(values=((True, 42), (False, 43)))
        """
        # TODO: check keyword?
        return cls(tuple(values))

    @classmethod
    def wrap(cls, v: T, ctx=smt.BoolVal(True)) -> "SymUnion[T]":
        """
        Wrap a value in a SymUnion. This is monadic pure/return
        >>> SymUnion.wrap(42)
        SymUnion(values=((True, 42),))
        """
        return cls(((ctx, v),))

    @classmethod
    def empty(cls) -> "SymUnion[T]":
        """
        The empty SymUnion. This is the identity for union and the annihilator for intersection.
        >>> SymUnion.empty()
        SymUnion(values=())
        """
        return cls(())

    # Is this useful? Why wouldn't you just call FreshBool? It's kind of interesting for roulette
    @staticmethod
    def flip() -> "SymUnion[bool]":
        """
        Flip a coin.

        >>> SymUnion.flip()
        SymUnion(values=((b!..., True), (Not(b!...), False)))
        """
        v = smt.FreshBool()
        return SymUnion.of_list([(v, True), (smt.Not(v), False)])

    def valueize(self: "SymUnion[smt.ExprRef]") -> "SymUnion[smt.ExprRef]":
        """
        Use smt solver to enumrate all possible models of the expression.
        """
        # TODO: Could add a optional keyword arg limit. Leave last one symbolic.
        values = []
        for ctx, expr in self.values:
            s = smt.Solver()
            if ctx is not None:
                s.add(ctx)
            v = smt.FreshConst(expr.sort())
            s.add(v == expr)
            while True:
                res = s.check()
                if res == smt.sat:
                    m = s.model()
                    val = m.eval(v, model_completion=True)
                    if ctx is not None:
                        cond = smt.And(ctx, expr == val)
                    else:
                        cond = expr == val
                    values.append((cond, expr2py(val)))
                    s.add(expr != val)
                elif res == smt.unsat:
                    break
                else:
                    raise ValueError("Solver returned unknown", expr)
        return SymUnion.of_list(values)

    def concretize(self: "SymUnion[smt.ExprRef]") -> "SymUnion[object]":
        """
        Turn a symbolic expression into all combinations of
        """
        return self.valueize().map(expr2py)

    def assume(self: "SymUnion[T]", cond: smt.BoolRef) -> "SymUnion[T]":
        """
        Add a guard to the SymUnion.
        The could also be called guard or project or perhaps filter.
        """
        # guard
        # TODO, hmm. Actually, the cond could optionally take in the value. Would that be useful?
        # Or cond could be a SymUnion
        return SymUnion.of_list([smt.And(cond, cond1) for cond1, v in self.values])

    def collect(self: "SymUnion[smt.ExprRef]") -> "SymUnion[smt.ExprRef]":
        """
        Collect via if-then-else chain all the branches into a single guarded expression.
        This is a merge of symbolic states into a single symbolic state.
        It internalizes the branching back into the solver

        >>> b = smt.Bool("b")
        >>> su = SymUnion.of_list([(b, 42), (smt.Not(b), 43)]).map(py2expr)
        >>> su.collect()
        SymUnion(values=((Or(b, Not(b)), If(b, 42, If(Not(b), 43, undef!...))),))
        """
        # collect into partial expressoin PartialExpr?
        if len(self.values) == 0:
            return SymUnion.empty()
        else:
            v = self.values[0][1]
            if not isinstance(v, smt.ExprRef):
                raise ValueError(
                    "collect only works on SymUnion of ExprRefs",
                    self,
                    "try x.map(pyexpr).collect()",
                )
            sort = v.sort()
        acc_expr = kd.Undef(sort)
        for cond, expr in reversed(self.values):
            acc_expr = smt.If(cond, expr, acc_expr)
        ctx = smt.Or([cond for cond, _ in self.values])
        return SymUnion.wrap(acc_expr, ctx=ctx)

    def prune(self: "SymUnion[T]") -> "SymUnion[T]":
        """
        Remove impossible conditions via smt query.

        >>> su = SymUnion.of_list([(smt.BoolVal(True), 42), (smt.BoolVal(False), 43)])
        >>> su.prune()
        SymUnion(values=((True, 42),))
        """
        new_values = []
        for cond1, v1 in self.values:
            s = smt.Solver()
            s.add(cond1)
            res = s.check()
            if res == smt.sat:
                new_values.append((cond1, v1))
            elif res == smt.unsat:
                pass
            else:
                raise ValueError("Solver returned unknown", cond1)
        return SymUnion.of_list(new_values)

    def map[U](self: "SymUnion[T]", f: Callable[[T], U]) -> "SymUnion[U]":
        return SymUnion.of_list([(k, f(v)) for k, v in self.values])

    def map2[U, V](
        self: "SymUnion[T]", other: "SymUnion[U]", f: Callable[[T, U], V]
    ) -> "SymUnion[V]":
        """
        Map a binary function over two SymUnions

        """
        new_values = []
        for cond1, v1 in self.values:
            # if cond1 in other.values: ? avoid loop join?
            for cond2, v2 in other.values:
                new_values.append((smt.And(cond1, cond2), f(v1, v2)))
        return SymUnion.of_list(new_values)

    def flatmap[U](
        self: "SymUnion[T]", f: Callable[[T], "SymUnion[U]"], strict=False
    ) -> "SymUnion[U]":
        new_values = []
        for cond1, v1 in self.values:
            su2 = f(v1)
            if isinstance(su2, SymUnion):
                for cond2, v2 in su2.values:
                    new_values.append((smt.And(cond1, cond2), v2))
            else:  # act like map if f doesn't return a SymUnion. Could instead fail
                if strict:
                    raise ValueError("Expected f to return a SymUnion", v1, su2)
                new_values.append((cond1, su2))
        return SymUnion.of_list(new_values)

    def join(self: "SymUnion[SymUnion[T]]") -> "SymUnion[T]":
        """
        Flatten a SymUnion of SymUnions. This is monadic join
        """
        new_values = []
        for cond1, su2 in self.values:
            for cond2, v2 in su2.values:
                new_values.append((smt.And(cond1, cond2), v2))
        return SymUnion.of_list(new_values)

    # operator overloads
    # https://docs.python.org/3/library/operator.html

    def __lt__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.lt)

    def __le__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.le)

    def __eq__(self, other: "SymUnion") -> "SymUnion":  # type: ignore
        return self.map2(other, operator.eq)

    def __ne__(self: "SymUnion", other: "SymUnion") -> "SymUnion":  # type: ignore
        return self.map2(other, operator.ne)

    def __ge__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.ge)

    def __add__(self, other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.add)

    def __and__(self, other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.and_)

    def __not__(self: "SymUnion") -> "SymUnion":
        return self.map(operator.not_)

    def __invert__(self: "SymUnion") -> "SymUnion":
        return self.map(operator.invert)

    def __lshift__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.lshift)

    def __mul__(self, other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.mul)

    def __matmul__(self, other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.matmul)

    def __neg__(self: "SymUnion") -> "SymUnion":
        return self.map(operator.neg)

    def __or__(self, other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.or_)

    def __pow__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.pow)

    def __rshift__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.rshift)

    def __sub__(self, other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.sub)

    def __truediv__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.truediv)

    def __xor__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.xor)

    def __getitem__(self: "SymUnion", key: "SymUnion") -> "SymUnion":
        return self.map2(key, operator.getitem)

    def __len__(self: "SymUnion") -> "SymUnion":
        return self.map(len)

    def __getattr__(self: "SymUnion", name: str) -> "SymUnion":
        # if name is _also_ a SymUnion, you are insane.
        return self.map(lambda v: getattr(v, name))

    def store(self: "SymUnion[tuple]", index: int, value: "SymUnion") -> "SymUnion":
        # TODO: index could also be symbolic.
        def _store(t, v):
            x = list(t)
            x[index] = v
            return tuple(x)

        return self.map2(value, _store)

    def _replace(self: "SymUnion", **kwargs) -> "SymUnion":
        # like dataclass replace but for SymUnion. Only works if the values are dataclasses. Could be useful for symbolic states.
        assert len(kwargs) == 1, "Only support replacing one field at a time for now"
        ((k, v),) = kwargs.items()
        return self.map2(v, lambda a, b: a._replace(k=b))

```

# Defocus from generics

From the outset knuckledragger has a terrible generics story. I'm shallowly based around smtlib and it doesn't even have parametric sorts. Z3 has sort of half support for type variables. I've seen some progress of parametric datatypes.

A big breath of fresh air was deciding to ignore this problem and just specialize to very concrete types. Ok, I'll prove theorems that are abstracted by filters over and over again. So what. Let's get the theorems, then think about whether it's worth it to make them DRY-er via some abstractions.

The thing that is tough is that the existing stuff in Lean, Isabelle, Rocq etc is completely soaked to the bone in genericity. They consider that to be kind of the game.

There are successful languages that aren't very generic (C, go). Some people abhor it, some love it. Seems like a missing corner of proof assistant design to me. Knuckledragger, the proof assistant for non abstracted neanderthals.

# What I want, What Others Want

No one uses Knuckledragger but me. I am somewhat committed to keep it easy to install, but I think I should shift to more of what I want and think is interesting rather than focus on stability for non existent users.

I had been conceiving of knuckledragger as a proof assistant for the every-programmer. But the every-programmer doesn't really want one. What I have learned about myself and the project is that actually I'm building the proof assistant for _me_. I both love and hate complexity and fanciness. I'm fascinated by the latest type theory doodad or even C++ but also abhor the complexity. My moods change. I like things simple. It is my belief that there is no concept that requires a language fancier than Python to explain. An the explanation suffers by refusing to engage with the closest thing we've got to a lingua franca of computing. Pseudo code is shorter and more creative, but suffers by it's non executability.

# Assembly Verification

My main applied project has been assembly verification. It is the only subproject that has enough external forcers that I'll push through once it becomes unpleasant.

Currently I have a symbolic executor of ghidra pcode which I can connect via bisimulation to a higher level model of the code written by a user as a transition relation/function. Then proofs can proceed at this higher level.

I was tearing my hair out trying to directly work with the output of the executor. This has been a much smoother experience so far. Z3 can basically automatically discharge the connection between the symbolic execution traces and the higher model (since really it's just the assembly with details about registers and flags and memory cleaned out. The analog of compiler IR)

<https://www.philipzucker.com/asm_verify4/>
