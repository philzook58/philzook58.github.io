---
title: Shallow Embedding Logics in Z3 pt. I
date: 2025-03-19
---

An interesting thing to do is try and embed one logical system into another. I typically am using smtlib in the form of z3, which is basically a classical higher order logic.

Some logics that are interesting:

- Temporal logic like TLA that have a built in notion of time <https://en.wikipedia.org/wiki/Temporal_logic>  <https://plato.stanford.edu/entries/logic-temporal/>
- Intuitionistic logic which is intrinsically more about constructions <https://en.wikipedia.org/wiki/Intuitionistic_logic>
- Separation Logic <https://en.wikipedia.org/wiki/Separation_logic> has an implicit heap / partial commutative monoid (disjoint heap join) that you can split using separating conjunction. cvc5 has built in support <https://cvc5.github.io/docs/cvc5-1.0.2/theories/separation-logic.html> but I'm still mostly focussed on z3.
- Linear Logic - propositions represent resources. <https://en.wikipedia.org/wiki/Linear_logic> An inspiration for memory management reasoning like in Rust.
- Fixed point logic - <https://en.wikipedia.org/wiki/Fixed-point_logic> special operators that enable defining things like transitive closure. Of relation to datalog
- Hoare logic - a logic for reasoning about programs <https://en.wikipedia.org/wiki/Hoare_logic> <https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html>
- Dynamic Logic - a relative of temporal logic <https://en.wikipedia.org/wiki/Dynamic_logic_(modal_logic)>
- Modal logics (of which temporal is an example). Provability
- Free logic - a built in notion of undefinedness / partiality  <https://en.wikipedia.org/wiki/Free_logic>
- Provability logic <https://plato.stanford.edu/entries/logic-provability/> Fun stuff.

For all logics (or modelling of any language), you can take a shallow or deep approach. In the deep approach, you make a datatype the model the syntax of the embedded logic. Then you make a provability relation over these trees say which moves of proof are allowed. Probably you also want a semantic interpreter that evaluates these trees into the basic stuff of your outer logic.

I tend to prefer shallow approaches because they use less boilerplate and can borrow more from the host system. In this case, I'd suspect the more shallow I am, the more z3's special solving capabilities might be able to handle it without lots of manual intervention.

These theories amongst others are starting to fill out the `theories` folder in knuckledragger, my low barrier z3 based proof assistant <https://github.com/philzook58/knuckledragger>

This is a lot to bite off for a single post, but we make baby steps

# Temporal

<https://github.com/philzook58/knuckledragger/blob/main/kdrag/theories/logic/temporal.py>

This is one style that I think is fairly natural. Using the built in z3 Ints is typically preferred to using algebraic nats <https://github.com/philzook58/knuckledragger/blob/main/kdrag/theories/nat.py> even if you kind of want nats because you get a lot of baked in reasoning for free.

Propositions are no longer Bool. Instead they are signals, bools predicates upon time. Aka `ArraySort(IntSort(), BoolSort())`. There may be advantages to not using a concrete int as time and instead using an abstract `DeclareSort("Time")` and an accessibility relation. Ints are totally ordered, which is only true in LTL <https://en.wikipedia.org/wiki/Linear_temporal_logic> (and TLA) but not in other varieties

I can mimic the interface of z3py `Const` `And` `Or` etc because I'm in a module namespace. Most of the logical operators apply componentwise.

```python
def Const(name, sort):
    return smt.Const(name, ArraySort(IntSort(), sort))
```

Some of the more interesting operators are

- `Next`  which just shifts a signal in time
- `Eventually` which exists quantifies over future time
- `Always` which forall quantifies over future time

To convert the `TBool` to a regular `Bool`, we can use `Valid` which asks if the formula is provable at time t=0

I think this is an interesting approach to embedding TLA+ model checking and the TLAPS proof system in python. I had a less principled approach I had considered before <https://www.philipzucker.com/Modelling_TLA_in_z3py/>
I note that Isabelle has a similar facility <https://isabelle.in.tum.de/library/HOL/HOL-TLA/TLA.html> . Isabelle is kind of crazy.

If it's of interest, I may fill out more TLA+ examples, and perhaps build a PlusCal layer

```python
import kdrag as kd
import kdrag.smt as smt
import functools
import operator


def lift_unop(S, op):
    def res(x):
        t = smt.FreshInt("t")
        return S(smt.Lambda([t], op(x.val)))

    return res


def lift_binop(S, op):
    def res(x, y):
        assert x.sort() == S
        y1 = smt._py2expr(y)
        if y1.sort() != S:
            y1 = TLift(y1)
            if y1.sort() != S:
                raise TypeError(f"Got {y} but expected expression of sort {S}")
        assert isinstance(y1, smt.DatatypeRef)
        t = smt.FreshInt("t")
        return S(smt.Lambda([t], op(x.val[t], y1.val[t])))

    return res


def Not(x: smt.DatatypeRef) -> smt.DatatypeRef:
    """
    >>> x = smt.Const("x", TSort(smt.BoolSort()))
    >>> smt.simplify(Valid(Not(x)))
    Not(val(x)[0])
    """
    t = smt.FreshInt("t")
    S = TSort(smt.BoolSort())
    return S(smt.Lambda([t], smt.Not(x.val[t])))


def Eq(x, y):
    """
    >>> x,y = smt.Consts("x y", TSort(smt.IntSort()))
    >>> smt.simplify(Valid(Eq(x,y)))
    val(x)[0] == val(y)[0]
    """
    t = smt.FreshInt("t")
    S = TSort(smt.BoolSort())
    return S(smt.Lambda([t], x.val[t] == y.val[t]))


def NEq(x, y):
    """
    >>> x,y = smt.Consts("x y", TSort(smt.IntSort()))
    >>> smt.simplify(Valid(NEq(x,y)))
    Not(val(x)[0] == val(y)[0])
    """
    t = smt.FreshInt("t")
    S = TSort(smt.BoolSort())
    return S(smt.Lambda([t], x.val[t] != y.val[t]))


@functools.cache
def TSort(sort):
    """
    Lift a sort to a sort that depends on time

    >>> TR = TSort(smt.RealSort())
    >>> x,y = smt.Consts("x y", TR)
    >>> _ = x + y
    >>> _ = x + TLift(2.1)
    """
    S = kd.NewType(f"T_{sort.name()}", smt.ArraySort(smt.IntSort(), sort))
    x, y = smt.Consts("x y", S)
    t = smt.Int("t")
    # kd.notation.add.register(S, lift_binop(S, operator.add))
    if sort == smt.IntSort() or sort == smt.RealSort() or sort in kd.notation.add:
        kd.notation.add.define([x, y], S(smt.Lambda([t], x.val[t] + y.val[t])))
    kd.notation.sub.register(S, lift_binop(S, operator.sub))
    kd.notation.mul.register(S, lift_binop(S, operator.mul))
    kd.notation.div.register(S, lift_binop(S, operator.truediv))
    kd.notation.and_.register(S, lift_binop(S, operator.and_))
    kd.notation.or_.register(S, lift_binop(S, operator.or_))
    kd.notation.invert.register(S, Not)
    kd.notation.eq.register(S, Eq)
    kd.notation.ne.register(S, NEq)
    kd.notation.getitem.register(S, lambda x, y: x.val[y])
    return S

    # kd.notation.eq.register(S, lift(operator.eq))


def is_T(x: smt.ExprRef) -> bool:
    """

    >>> x = Int("x")
    >>> is_T(x)
    True
    >>> is_T(TLift(1))
    True
    >>> is_T(smt.BoolVal(True))
    False
    """
    return x.sort().name().startswith("T_")


TBool = TSort(smt.BoolSort())
TInt = TSort(smt.IntSort())
TReal = TSort(smt.RealSort())
TString = TSort(smt.StringSort())

x, y = smt.Consts("x y", TInt)
t = smt.Int("t")
kd.notation.ge.define([x, y], TBool(smt.Lambda([t], x.val[t] >= y.val[t])))
kd.notation.le.define([x, y], TBool(smt.Lambda([t], x.val[t] <= y.val[t])))


def Bool(name: str) -> smt.DatatypeRef:
    """
    Create a Boolean signal

    >>> x = Bool("x")
    >>> _ = x & True
    """
    return smt.Const(name, TBool)


def Bools(names: str) -> list[smt.DatatypeRef]:
    """
    Create a list of Boolean signals

    >>> x, y = Bools("x y")
    >>> _ = x & y
    """
    return smt.Consts(names, TBool)


def Int(name: str) -> smt.DatatypeRef:
    """
    Create an integer signal

    >>> x = Int("x")
    >>> _ = x + TLift(1)
    """
    return smt.Const(name, TInt)


def Ints(names: str) -> list[smt.DatatypeRef]:
    """
    Create a list of Integer signals

    >>> x, y = Ints("x y")
    >>> _ = x + y
    """
    return smt.Consts(names, TInt)


def TLift(n: smt.ExprRef | int | str) -> smt.DatatypeRef:
    """
    Lift a value into a constant signal

    >>> TLift(1)
    T_Int(K(Int, 1))
    >>> TLift(True)
    T_Bool(K(Int, True))
    """
    n = smt._py2expr(n)
    return TSort(n.sort())(smt.K(smt.IntSort(), n))


def And(*args):
    """
    >>> _ = And(TLift(True), TLift(False))
    """
    assert all(x.sort() == TBool for x in args)
    if len(args) == 0:
        return TLift(smt.BoolVal(True))
    elif len(args) == 1:
        return args[0]
    return functools.reduce(operator.and_, args)


def Or(*args):
    """

    >>> _ = Or(TLift(True), TLift(False))
    """
    assert all(x.sort() == TBool for x in args)
    if len(args) == 0:
        return TLift(smt.BoolVal(False))
    elif len(args) == 1:
        return args[0]
    return functools.reduce(operator.or_, args)


def Next(x):
    """

    >>> x = smt.Const("x", TSort(smt.BoolSort()))
    >>> Next(x)
    T_Bool(Lambda(t!..., val(x)[t!... + 1]))
    """
    t = smt.FreshInt("t")
    S = x.sort()
    return S(smt.Lambda([t], x.val[t + 1]))


def X(p):
    return Next(p)


def Always(x: smt.DatatypeRef, vs=None) -> smt.DatatypeRef:
    """
    Returns the TBool signal that x is always true after time t (inclusive).

    >>> t = smt.Int("t")
    >>> s = TBool(smt.Lambda([t], t >= 1))
    >>> _ = kd.prove(smt.Not(Valid(Always(s))))
    >>> _ = kd.prove(Valid(Always(Next(s))))
    """
    assert x.sort() == TBool
    if vs is not None:
        x = Or(x, And(*[UNCHANGED(v) for v in vs]))
    t = smt.FreshInt("t")
    dt = smt.FreshInt("dt")
    S = x.sort()
    return S(smt.Lambda([t], kd.QForAll([dt], dt >= 0, x.val[t + dt])))


def G(x, vs=None):
    return Always(x, vs=vs)


def Eventually(x):
    assert x.sort() == TBool
    t = smt.FreshInt("t")
    dt = smt.FreshInt("dt")
    S = x.sort()
    return S(smt.Lambda([t], kd.QExists([dt], dt >= 0, x.val[t + dt])))


def F(x):
    return Eventually(x)


def If(c: smt.DatatypeRef, x: smt.DatatypeRef, y: smt.DatatypeRef) -> smt.DatatypeRef:
    """
    >>> _ = If(TLift(True), TLift(1), TLift(2))
    """
    t = smt.FreshInt("t")
    assert x.sort() == y.sort()
    assert c.sort() == TBool
    S = x.sort()
    return S(smt.Lambda([t], smt.If(c.val[t], x.val[t], y.val[t])))


def Implies(x: smt.DatatypeRef, y: smt.DatatypeRef) -> smt.DatatypeRef:
    """
    >>> x,y = smt.Consts("x y", TSort(smt.BoolSort()))
    >>> smt.simplify(Valid(Implies(x, y)))
    Or(Not(val(x)[0]), val(y)[0])
    """
    return lift_binop(x.sort(), smt.Implies)(x, y)


def UNCHANGED(p: smt.DatatypeRef) -> smt.DatatypeRef:
    """
    Returns the TBool representing that signal at time t equals signal at time t + 1

    >>> smt.simplify(Valid(UNCHANGED(TLift(1))))
    True
    """
    return Eq(Next(p), p)


def Valid(p: smt.DatatypeRef) -> smt.BoolRef:
    """
    The statement that the formula is true at `t = 0`.
    Convert a temporal formula into a Boolean.
    https://en.wikipedia.org/wiki/Kripke_semantics#Semantics_of_modal_logic

    """
    return p.val[0]


# Internal definitions for abstraction

p, q = smt.Consts("p q", TBool)
tnot = kd.define("tnot", [p], Not(p))
tand = kd.define("tand", [p, q], And(p, q))
tor = kd.define("tor", [p, q], Or(p, q))
timpl = kd.define("timpl", [p, q], Implies(p, q))
implies = timpl
eventually = kd.define("eventually", [p], Eventually(p))
always = kd.define("always", [p], Always(p))
bnext = kd.define("next", [p], Next(p))
beq = kd.define("beq", [p, q], Eq(p, q))
valid = kd.define("valid", [p], Valid(p))
valid_and = kd.prove(
    smt.ForAll([p, q], valid(tand(p, q)) == smt.And(valid(p), valid(q))),
    by=[valid.defn, tand.defn],
)
valid_or = kd.prove(
    smt.ForAll([p, q], valid(tor(p, q)) == smt.Or(valid(p), valid(q))),
    by=[valid.defn, tor.defn],
)
valid_impl = kd.prove(
    smt.ForAll([p, q], valid(timpl(p, q)) == smt.Implies(valid(p), valid(q))),
    by=[valid.defn, timpl.defn],
)
valid_not = kd.prove(
    smt.ForAll([p, q], valid(tnot(p)) == smt.Not(valid(p))),
    by=[valid.defn, tnot.defn],
)


x, y = smt.Consts("x y", TInt)
ieq = kd.define("ieq", [x, y], Eq(x, y))
ineq = kd.define("ineq", [x, y], NEq(x, y))
inext = kd.define("inext", [x], Next(x))
if_int = kd.define("if_int", [p, x, y], If(p, x, y))
x = smt.Int("x")
tint = kd.define("tint", [x], TInt(smt.K(smt.IntSort(), x)))
# annoyingly polymorphic
# tif = kd.define("tif", [p, q, r], If(p, q, r))
# teq
# tiff = kd.define("tiff", [p, q], smt.Eq(p, q))
```

A sketch of what the Clock spec may look like <https://github.com/tlaplus/Examples/blob/master/specifications/SpecifyingSystems/RealTime/HourClock.tla>

```python
import kdrag.theories.logic.temporal as tla
hr = tla.Int("hr")
HCini = tla.tand(tla.tint(1) <= hr, hr <= tla.tint(12))
HCini = kd.define("HCini", [], HCini)
#kd.rewrite.simp(HCini)
HCnxt = tla.ieq(tla.inext(hr), tla.if_int(tla.ineq(hr, tla.tint(12)), hr + tla.tint(1), tla.tint(1)))
HCnxt = kd.define("HCnxt", [], HCnxt)
kd.rewrite.simp(HCnxt)
#kd.rewrite.simp(tla.Valid(tla.Always(tla.Next(hr) == HCnxt, vs=[hr])))
#HC = tla.tand(HCini, tla.always(HCnxt, vs=[hr]))
HC = tla.tand(HCini, tla.always(HCnxt))
thm = tla.valid(tla.implies(HC, tla.always(HCini)))
# and then to actually go on an prove it
```

# Intuitionistic

Intuitionistic logic actually has a Kripke semantics. <https://en.wikipedia.org/wiki/Kripke_semantics#Semantics_of_intuitionistic_logic>

Kripke semantics makes truth predicated on which world you are on. Depending on which logic you are using, there is some relation between the accessibility relation between worlds and how thing are true.

The intuitionistic kripke model is monotonic in that worlds are preordered and the number of true things only grows when you access new worlds. This is very evocative of the construction or theorem proving process itself, although I'm not sure of a sense in which to make that precise.

THe way I did this in knuckledragger is to use a `NewType` with a predicate around the `World -> Bool` function that asserts that well formed propsitions ought to grow monotonically. These predicates are registered and auto inserted when you use `QExists` and `QForAll`. It's a lightweight, kind of janky refinement type replacement. But it works ok. THe main interesting connective which isn't completely pointwise defined is `Implies`. It kind of needs to encode the promise that implication holds at all future worlds.

I believe I can extend to first order intuitionstic logic by representing other sorts `A` as "signals" `World -> Set(A)` where the set has to monotonically grow with time.

This encoding does prove simple theorem in a single automated shot and is incapable of proving double negation elimination and law of excluded middle. It actually does show a two world countermodel to excluded middle. Pretty cool.

I assume single shot solving starts to choke as the depth of `implies` gets deeper. That's were the badness happens. But the point of knuckledragger is to guide the system through those problems. That is why I have both Capitalized version of functions which macro expand the definition in the python layer and the lower case version which use the knuckeldragger define system to optionally hide and abstract away the internals of definitions of things like `and` `or` `implies`.

<https://github.com/philzook58/knuckledragger/blob/main/kdrag/theories/logic/intuitionistic.py>

<https://easychair.org/publications/paper/8jNL/open> Embedding Intuitionistic into Classical Logic. Comparing a couple different approaches to using classical theorem provers for intuitionistic logic.

```python
import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.set as set_
import functools
# https://plato.stanford.edu/Entries/logic-intuitionistic/#FormSystMathMath
# https://en.wikipedia.org/wiki/Kripke_semantics#Semantics_of_intuitionistic_logic
# def modus(A : smt.BoolRef, AB : smt.BoolRef) -> kd.Proof:
#    return kd.axiom(smt.Implies(A, smt.Implies(AB, A)))

"""
A different approach. Direct axiomatization of an uninterpreted sort.
Prop = smt.DeclareSort("Prop")
A, B = smt.Consts("A B", Prop)
Implies = smt.Function("Implies", Prop, Prop, Prop)
And = smt.Function("And", Prop, Prop, Prop)
Or = smt.Function("Or", Prop, Prop, Prop)
Not = smt.Function("Not", Prop, Prop)
modus = kd.axiom(kd.QForAll([A, B], Implies(A, Implies(A, B), B)))

Another approach might be to make a datatype of intuitionistic syntax trees.

"""

World = smt.DeclareSort("World")
w, u, v = smt.Consts("w u v", World)
acc = smt.Function("acc", World, World, smt.BoolSort())
# acc0 = smt.Function("acc0", World, smt.BoolSort())
# accplus = smt.TransitiveClosure(acc0)
# acc = smt.Lambda([w,u], smt.Or(w == u, accplus(w,u)))
acc_refl = kd.axiom(smt.ForAll([w], acc(w, w)))
acc_trans = kd.axiom(kd.QForAll([w, u, v], acc(w, u), acc(u, v), acc(w, v)))

Prop = kd.NewType(
    "Prop",
    smt.ArraySort(World, smt.BoolSort()),
    pred=lambda p: kd.QForAll([w, u], acc(w, u), p.val[w], p.val[u]),
)
"""
A proposition is a world valuation function. Propositions become monotonically more true as we move to more accessible worlds.
Note that Prop ~ Sort(Unit)
"""


def And(*ps: smt.DatatypeRef) -> smt.DatatypeRef:
    """
    w |= (A /\\ B)[e] if and only if w |= A[e] and w |= B[e]

    >>> p, q = smt.Consts("p q", Prop)
    >>> And(p,q)
    Prop(Lambda(w, And(val(p)[w], val(q)[w])))
    """
    return Prop(smt.Lambda([w], smt.And(*[p.val[w] for p in ps])))


def Or(*ps: smt.DatatypeRef) -> smt.DatatypeRef:
    """
    w |= (A \\/ B)[e] if and only if w |= A[e] or w |= B[e]

    >>> p, q = smt.Consts("p q", Prop)
    >>> Or(p,q)
    Prop(Lambda(w, Or(val(p)[w], val(q)[w])))
    """
    return Prop(smt.Lambda([w], smt.Or(*[p.val[w] for p in ps])))


def Implies(p: smt.DatatypeRef, q: smt.DatatypeRef) -> smt.DatatypeRef:
    return Prop(
        smt.Lambda([w], kd.QForAll([u], acc(w, u), smt.Implies(p.val[u], q.val[u])))
    )


TRUE = Prop(smt.K(World, smt.BoolVal(True)))
FALSE = Prop(smt.K(World, smt.BoolVal(False)))


def Not(p: smt.DatatypeRef) -> smt.DatatypeRef:
    return Implies(p, FALSE)


def Valid(p: smt.DatatypeRef) -> smt.BoolRef:
    return smt.ForAll([w], p.val[w])


@functools.cache
def Sort(sort: smt.SortRef):
    return kd.NewType(
        f"I_{sort}",
        smt.ArraySort(World, set_.Set(sort)),
        pred=lambda x: kd.QForAll([w, u], acc(w, u), x.val[w] <= x.val[u]),
    )


def Const(name: str, sort: smt.SortRef) -> smt.DatatypeRef:
    raise NotImplementedError


# def Exists(xs, body):

a, b, c = smt.Consts("a b c", Prop)
and_ = kd.define("iand", [a, b], And(a, b))
or_ = kd.define("ior", [a, b], Or(a, b))
impl_ = kd.define("iimpl", [a, b], Implies(a, b))
not_ = kd.define("inot", [a], Not(a))
valid = kd.define("valid", [a], Valid(a))

kd.notation.and_.register(Prop, and_)
kd.notation.or_.register(Prop, or_)
kd.notation.invert.register(Prop, not_)

impl_aba = kd.prove(kd.QForAll([a, b], valid(impl_(a, impl_(b, a)))), unfold=1)


impl_aba = kd.prove(kd.QForAll([a, b], Valid(Implies(a, Implies(b, a)))))
and_elim1 = kd.prove(kd.QForAll([a, b], Valid(Implies(And(a, b), a))))
and_elim2 = kd.prove(kd.QForAll([a, b], Valid(Implies(And(a, b), b))))
or_intro1 = kd.prove(kd.QForAll([a, b], Valid(Implies(a, Or(a, b)))))
or_intro2 = kd.prove(kd.QForAll([a, b], Valid(Implies(b, Or(a, b)))))
# fails dne = kd.prove(kd.QForAll([a], Valid(Implies(Not(Not(a)), a))))

# Non theorems. Raise errors. See Tests

# Mmm. Maybe this isn't enough to show a non provability?
# excluded_middle = kd.prove(
#    smt.Not(kd.QForAll([a], Valid(Or(a, Not(a))))), by=[acc_refl, acc_trans]
# )
# dne = kd.prove(kd.QForAll([a], Valid(Implies(Not(Not(a)), a))))

"""
Finite model property + 
"""
```

A two world countermodel to excluded middle. I had to rip the thing apart to print the model in an interpretable way. Not ideal.

```python
from kdrag.all import *
import kdrag.theories.logic.intuitionistic as I
a,b,c = smt.Consts("a b c", I.Prop)
s = smt.Solver()
s.add(smt.Not(I.Valid(I.Or(a, I.Not(a)))))
s.add(a.wf())
s.add([I.acc_refl.thm, I.acc_trans.thm])
a1 = smt.Function("a", I.World, smt.BoolSort())
w = smt.Const("w", I.World)
s.add(smt.ForAll([w], a1(w) == a.val(w)))
print(s.check())
m = s.model()
Worlds = m[I.World]
print("a" , [(w, m.eval(a.val(w))) for w in Worlds])
print("acc", {(w,u) : m.eval(I.acc(w,u)) for w in Worlds for u in Worlds})
```

# Bits and Bobbles

Logikey is doing something like the above by embedding in isabelle and using Isabelle's sledgehammer <https://arxiv.org/abs/2502.19311> Faithful Logic Embeddings in HOL -- A recipe to have it all: deep and shallow, automated and interactive, heavy and light, proofs and counterexamples, meta and object level - benzmuller. <https://arxiv.org/abs/1903.10187>

<https://x.com/SandMouth/status/1895882800064315493>
<https://x.com/SandMouth/status/1557140546036142081>

I got pretty confused attempting a shallow embedding of Linear Logic.

If you start in an intuitionistic system, it is easy to model classical logic via adding an axiom. Intuitionistic (or minimal) logic has the option to be extra super shallow in this way. The double negation translation or using a model is a shallow embedding in a style that most other systems can emulate

I did not always know this, but there isn't really one thing called logic. <https://en.wikipedia.org/wiki/Logic> My impression of logic is that it is boolean logic, the thing you can make electrical circuits to mimic and can write as boolean expressions in programming languages. You have `and`, `or`, `not`, `implies`. Combining these pieces you can encode bitvectors representing operations on integers, which is pretty cool.

A different perspective I became aware of is that formal logic is the syntactic manipulation of logical statements <https://en.wikipedia.org/wiki/Logic#Formal_logic> . In particular, I think of logical statements as being some syntax tree I can express in python lets say, and the manipulations being python functions I can write over them to change them, break them apart, or build new expressions in different ways.

Axioms are just a collection of statements you are allowed to start with and the process of proving is just different ways of combining these meaningless things.

And yet, I am not inclined to say that any arbitrary transition system is "logic". I kind of want it to connect to some intuitive thing that feels like reasoning. The pieces of syntax and the moves you can make should correspond to english sentences that feel reasoning-y. One way of putting this is that I want to be able to write a python function that can recurse down the tree or along a proof and pretty print and english sentence.

The more rigorous form of this idea is if I make my syntax tree datatype in a language like Lean. Then the language having meaning is the ability to intepret the syntax tree into leans logic by a function `interp: Formula -> Prop` and the ability to turn my systems proofs into lean's built in notion of proof. `forall fm : Formula, MyProof fm -> interp fm`

Classical logic does not have a complete stranglehold on what is a logic. It is good for a certain kind of abstract mathematical reasoning. But modal logics may be a useful abstraction for reasoning that involves time or uncertainty.

- Separation and linear logic may be useful for reasoning involving notions of resources being used. Non-monotonic logic
- Fixed point logic.

I do think of classical and intuitionistic logic as being kind of special and these other logics

You can model other logics in your system via a shallow or deep approach.  <https://proofassistants.stackexchange.com/questions/2499/what-is-a-deep-embedding-vs-a-shallow-embedding-with-examples>

Deep means you embed an entire syntax tree and build interpreters out of it.

Shallow means you build combinators that directly manipulate the stuff of your meta language. You directly manipulate meaning. They are a deforesting of deep embeddings. I vaguely associate the tricks needed to do this sort of thing with finally tagless style programming and Bohm Berarducci / Church encodings.

The terms also come up in domain specific languages (DSLs) which have many of the same design considerations and tradeoffs.

I more or less prefer shallow embeddings because deep embeddings basically require twice as much code. On the flipside, in some respects shallow embeddings require a little bit of trickery and may be less readable. It also may be difficult or impossible to prove metatheorems about your shallow embedding, because this may involve your meta language proving meta theorems about itself.

If your language of formulas or proofs has a notion of binder (lambda, forall, exists), deep embeddings are going to have a bunch of fiddly boilerplate. There are kind of mixed styles like HOAS / PHOAS which borrow the host binders but still have reified syntax trees.

For emebedding other logics in Knuckledragger, either is doable. I can directly make tree datatypes using `kd.Inductive`.

I have found it kuind of nice (as I often do) to go shallow.

# separation

IRis
<https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf>

```
And here's the paper with a nice clean separation logic semantics, with explicit connections to Kripke frames: https://www.cs.princeton.edu/~appel/papers/bringing-order.pdf/. The corresponding models of relevance logic are Routley-Myers models. The distinctive feature of the signature is the same in both cases (a three-place relation R), and the semantics for the relevant conditional are exactly Cao-Culler-Appel's weak semantics for the wand. But there are a lot of other constraints that are different (Routley-Meyers assumes a distinguished element 0 s.t. R0ab iff a<b, so they don't have < as an extra part of a model's signature. Cao-Culler-Appel makes < part of the signature. Cao-Culler-Appel assumes that Rabc implies Rbac, and this isn't built in to all relevance logics)
```

My old post.

asbtract locations rather than integers?
DeclareSort("Loc")

DeclareSort("Heap") abstract heap? monoid?

# linear logic

resource interpretation
Propositions ~ Nat

but we move between "world". World -> Nat?

Intuitionsitc is monotonic growth?

Hodas, J., and Miller, D., 1994, “Logic programming in a fragment of intuitionistic linear logic”, Information and Computation, 110(2): 327–365.

Kr r indexed set of kripke interpretations... hmm.

Exmaple commutative monoids could be nats. vector of nats.

but separation logic is a different monoid?

```python
from kdrag.all import *


World = smt.DeclareSort("LinWorld")
acc
Prop = kd.NewType('Prop', smt.Array(World, smt.IntSort()), pred=lambda x: smt.ForAll([n], x[n] >= 0))
A,B,C = smt.Consts('A B C', Prop)

def Bang(x):
    """convert into classical logic? Convert into intuitionsitc logic"""
    smt.QExists([x], x)

TRUE = smt.IntVal(1) #? Or should it be infinity?


def SumAnd(): ...
def SumOr(): ...
def MulAnd(): ...
def MulOr():
        pass

def Lolli(A, B):
    return smt.Implies(A, B)


```

# TLA+

<https://www.philipzucker.com/Modelling_TLA_in_z3py/>
Alloy
Quintus

<https://www.learntla.com/introduction/>

Lift everything to signals
<https://news.ycombinator.com/item?id=41382828>

I need to hide everything under the abstract definitions so that it is readable.
The conversio nin simplify  of implies to no

Ah. This _does_ require induction.

<https://lamport.azurewebsites.net/tla/book-02-08-08.pdf> specifying systems

There is a tla in isabelle.

```python
from kdrag.all import *
import kdrag.theories.logic.temporal as tla

hr = tla.Int("hr")
HCini = tla.tand(tla.tint(1) <= hr, hr <= tla.tint(12))
HCini = kd.define("HCini", [], HCini)
#kd.rewrite.simp(HCini)
HCnxt = tla.ieq(tla.inext(hr), tla.if_int(tla.ineq(hr, tla.tint(12)), hr + tla.tint(1), tla.tint(1)))
HCnxt = kd.define("HCnxt", [], HCnxt)
kd.rewrite.simp(HCnxt)
#kd.rewrite.simp(tla.Valid(tla.Always(tla.Next(hr) == HCnxt, vs=[hr])))
#HC = tla.tand(HCini, tla.always(HCnxt, vs=[hr]))
HC = tla.tand(HCini, tla.always(HCnxt))
thm = tla.valid(tla.implies(HC, tla.always(HCini)))
thm
#kd.rewrite.simp(thm)



```

valid(timpl(tand(HCini, always(HCnxt)), always(HCini)))

```python
# intermiedate lemma
l = kd.Lemma(tla.valid(tla.always(tla.implies(tla.tand(HCini, HCnxt),  HCini))))

```

```python
p, q = smt.Consts("p q", tla.TBool)
valid_and = kd.prove(smt.ForAll([p,q], tla.valid(tla.tand(p, q)) == smt.And(tla.valid(p), tla.valid(q))), by=[tla.valid.defn, tla.tand.defn])
valid_or = kd.prove(smt.ForAll([p,q], tla.valid(tla.tor(p, q)) == smt.Or(tla.valid(p), tla.valid(q))), by=[tla.valid.defn, tla.tor.defn])
valid_impl = kd.prove(smt.ForAll([p,q], tla.valid(tla.timpl(p,q)) == smt.Implies(tla.valid(p), tla.valid(q))), by=[tla.valid.defn, tla.timpl.defn])
valid_not = kd.prove(smt.ForAll([p,q], tla.valid(tla.tnot(p)) == smt.Not(tla.valid(p))), by=[tla.valid.defn, tla.tnot.defn])

tand_0 = kd.prove(smt.ForAll([p], tla.tand(p,q)[0] == smt.And(p[0], q[0])), by=[tla.tand.defn])
tor_0 = kd.prove(smt.ForAll([p], tla.tor(p,q)[0] == smt.Or(p[0], q[0])), by=[tla.tor.defn])

t = smt.Int("t")
tand_t = kd.prove(smt.ForAll([p,q,t], tla.tand(p,q)[t] == smt.And(p[t], q[t])), by=[tla.tand.defn])
tor_t = kd.prove(smt.ForAll([p,q,t], tla.tor(p,q)[t] == smt.Or(p[t], q[t])), by=[tla.tor.defn])
timpl_t = kd.prove(smt.ForAll([p,q,t], tla.timpl(p,q)[t] == smt.Implies(p[t], q[t])), by=[tla.timpl.defn])
tnot_t = kd.prove(smt.ForAll([p,t], tla.tnot(p)[t] == smt.Not(p[t])), by=[tla.tnot.defn])

# one step unfold
always_t = kd.prove(smt.ForAll([p,t], tla.always(p)[t] == smt.And(p[t], tla.always(p)[t+1])), by=[tla.always.defn])

```

```python
always_next = kd.prove(smt.ForAll([p], tla.valid(tla.always(p)) == smt.And(tla.valid(p), tla.valid(tla.always(tla.bnext(p))))),
                        by=[tla.always.defn, tla.bnext.defn, tla.valid.defn])
```

    ---------------------------------------------------------------------------

    LemmaError                                Traceback (most recent call last)

    File ~/Documents/python/knuckledragger/kdrag/tactics.py:164, in prove(thm, by, admit, timeout, dump, solver, defns, simps)
        163 try:
    --> 164     return kd.kernel.prove(
        165         thm, by, timeout=timeout, dump=dump, solver=solver, admit=admit
        166     )
        167 except kd.kernel.LemmaError as e:


    File ~/Documents/python/knuckledragger/kdrag/kernel.py:118, in prove(thm, by, admit, timeout, dump, solver)
        117         raise LemmaError(thm, "Countermodel", s.model())
    --> 118     raise LemmaError("prove", thm, res)
        119 else:


    LemmaError: ('prove', ForAll(p,
           valid(always(p)) ==
           And(valid(p), valid(always(next(p))))), unknown)

    
    During handling of the above exception, another exception occurred:


    LemmaError                                Traceback (most recent call last)

    Cell In[7], line 1
    ----> 1 always_next = kd.prove(smt.ForAll([p], tla.valid(tla.always(p)) == smt.And(tla.valid(p), tla.valid(tla.always(tla.bnext(p))))),
          2                         by=[tla.always.defn, tla.bnext.defn, tla.valid.defn])


    File ~/Documents/python/knuckledragger/kdrag/tactics.py:176, in prove(thm, by, admit, timeout, dump, solver, defns, simps)
        174     _, thm = kd.utils.open_binder_unhygienic(thm)  # type: ignore
        175 # We anticipate this failing with a better countermodel since we can now see the quantified variables
    --> 176 pf = kd.kernel.prove(
        177     thm, by=by, timeout=timeout, dump=dump, solver=solver, admit=admit
        178 )
        179 # TODO: Maybe we should herbrandize and just let the quantifier free version work for us.
        180 raise Exception(
        181     "Worked with quantifier stripped. Something is going awry", pf
        182 )


    File ~/Documents/python/knuckledragger/kdrag/kernel.py:118, in prove(thm, by, admit, timeout, dump, solver)
        116     if res == smt.sat:
        117         raise LemmaError(thm, "Countermodel", s.model())
    --> 118     raise LemmaError("prove", thm, res)
        119 else:
        120     return Proof(thm, list(by), False)


    LemmaError: ('prove', valid(always(p)) == And(valid(p), valid(always(next(p)))), unknown)

```python
l = kd.Lemma(smt.ForAll([p], tla.valid(tla.always(p)) == smt.And(tla.valid(p), tla.valid(tla.always(tla.bnext(p))))))
p = l.fix()
l.unfold()
l.simp()
l.split()

l.intros()
l.split(-1)
dt = l.fix()
l.instan(1, dt-1)
l.auto()

#l.intros()
l.auto()

always_unfold = l.qed()


```

&#8870;ForAll(p!6016,
       valid(always(p!6016)) ==
       And(valid(p!6016), valid(always(next(p!6016)))))

```python
kd.prove(smt.ForAll([p], tla.valid(tla.tnot(tla.always(p))) == tla.valid(tla.eventually(tla.tnot(p)))), 
         by = [tla.valid.defn, tla.tnot.defn, tla.always.defn, tla.eventually.defn])
```

    ---------------------------------------------------------------------------

    LemmaError                                Traceback (most recent call last)

    File ~/Documents/python/knuckledragger/kdrag/tactics.py:164, in prove(thm, by, admit, timeout, dump, solver, defns, simps)
        163 try:
    --> 164     return kd.kernel.prove(
        165         thm, by, timeout=timeout, dump=dump, solver=solver, admit=admit
        166     )
        167 except kd.kernel.LemmaError as e:


    File ~/Documents/python/knuckledragger/kdrag/kernel.py:118, in prove(thm, by, admit, timeout, dump, solver)
        117         raise LemmaError(thm, "Countermodel", s.model())
    --> 118     raise LemmaError("prove", thm, res)
        119 else:


    LemmaError: ('prove', ForAll(p!6033,
           valid(tnot(always(p!6033))) ==
           valid(eventually(tnot(p!6033)))), unknown)

    
    During handling of the above exception, another exception occurred:


    LemmaError                                Traceback (most recent call last)

    Cell In[40], line 1
    ----> 1 kd.prove(smt.ForAll([p], tla.valid(tla.tnot(tla.always(p))) == tla.valid(tla.eventually(tla.tnot(p)))), by = [tla.valid.defn, tla.tnot.defn, tla.always.defn, tla.eventually.defn])


    File ~/Documents/python/knuckledragger/kdrag/tactics.py:176, in prove(thm, by, admit, timeout, dump, solver, defns, simps)
        174     _, thm = kd.utils.open_binder_unhygienic(thm)  # type: ignore
        175 # We anticipate this failing with a better countermodel since we can now see the quantified variables
    --> 176 pf = kd.kernel.prove(
        177     thm, by=by, timeout=timeout, dump=dump, solver=solver, admit=admit
        178 )
        179 # TODO: Maybe we should herbrandize and just let the quantifier free version work for us.
        180 raise Exception(
        181     "Worked with quantifier stripped. Something is going awry", pf
        182 )


    File ~/Documents/python/knuckledragger/kdrag/kernel.py:118, in prove(thm, by, admit, timeout, dump, solver)
        116     if res == smt.sat:
        117         raise LemmaError(thm, "Countermodel", s.model())
    --> 118     raise LemmaError("prove", thm, res)
        119 else:
        120     return Proof(thm, list(by), False)


    LemmaError: ('prove', valid(tnot(always(p!6033))) ==
    valid(eventually(tnot(p!6033))), unknown)

```python

```

I want it to always refold stuff.
So I should rearrange my definitions to be in terms of...
No these are the extensionally lifted definitions. Hmm.
That's why I kept unfolding and simp.
But simp also mushes around boolean connectives, which I don't love

Yeah, lambda stuff is kind of defined observationally actually.

```python
def ext_defn(f):
    f.defn
```

```python

import kdrag.theories.int as int_
l = kd.Lemma(thm)
l.unfold(tla.valid)
l.unfold(tla.timpl, tla.tand)
l.simp()
l.intros()
l.split(0)

l.unfold(tla.always)
l.simp()
dt = l.fix()
#l.intros()
l.induct(dt)
l.auto() # < 0
l.auto() # = 0

n = l.fix()
l
l.intros()
l.split(-1)
l.unfold(tla.always)
```

    [dt!19, n!23];
    [val(HCini)[0],
     val(always(HCnxt))[0],
     n!23 >= 0,
     Lambda(dt!19, Or(Not(dt!19 >= 0), val(HCini)[dt!19]))[n!23]]
    ?|- Lambda(dt!19, Or(Not(dt!19 >= 0), val(HCini)[dt!19]))[n!23 +
      1]

```python
import kdrag as kd
from kdrag.smt import *

Signal = kd.smt.ArraySort(IntSort(), BoolSort())
n = smt.Const("n", IntSort())
next = kd.define("next", [x], smt.Lambda([x], x[n-1]))

def TConst(name, sort):
    return Const(name, smt.ArraySort(IntSort(), sort))
def TConsts(name, sort):
    return Consts(name, smt.ArraySort(IntSort(), sort))
x,y,z = TConsts("x y z", BoolSort())

def TAnd(*args):
    return Lambda([n], And([arg[n] for arg in args]))

INIT = Const("INIT", Signal)
def BOX(f):
    return Lambda([m], ForAll([n], n >= m, f[n]))
ALWAYS = BOX

BOX = kd.define("[]", [f], BOX(f))

def lower(t):
    return t[0]

lower(TAnd(INIT, Box(next(x) == x)))

LabelSort = EnumSort("LABEL", "L1 L2 L3 L4")
LABEL = TConst("LABEL", LabelSort)


def bounded(n):
    # knuckeldragger could understand that the forall property implies the bounded property
    # And then separaetly to the bounded property.
    return kd.lemma(ForAll[P], Implies(Box(P), And([P(n) for i in range(n)]) ))



hr = TConst("hr", IntSort())
HCini = TAnd(hr >= 1, hr <= 12)
HCnxt = next(hr) == TIf(hr == 12, 1, hr + 1)
HC = TAnd(HCini, Box(HCnxt))

```

Differentiation and Platzer's stuff.
ODEs

```python

```

# Intuitionistic Knuckle

Deep embedding vs new kernel

Abstract proof theory

```python
from kdrag.all import *

# Proofs are kind of open datatype conitaing subproofs and 
Proof = smt.DeclareSort("Proof")
prop = Function("prop", Proof, Prop)
# open datatype? Closed?
Prop = smt.DeclareSort("Prop")
impl = Function("impl", Prop, Prop)
is_impl = Function("is_impl", Prop, BoolSort())


# The semantic interpretation of impl is a function
def Impl(a,b): return ArraySort(Proof, Proof)
# a partial function though.
ArraySort(Proof,Proof,Proof,BoolSort())
ArraySort(Proof,Option(Proof))



wf = Function("wf", Proof, BoolSort())
kd.notation.wf.register(Proof, wf)





```

```python

```

    sat
    a [(World!val!1, True), (World!val!0, False)]
    acc {(World!val!1, World!val!1): True, (World!val!1, World!val!0): False, (World!val!0, World!val!1): True, (World!val!0, World!val!0): True}

```python
class Proof():
    subproofs : list["Proof"] 
    hyps: list[smt.BoolRef]
    conc: smt.BoolRef

def impE(pfab, pfa):
    pfab.conc 
    hyps = pfab.hyps + [pfab.conc]
    conc = pfa.conc
    return Proof([pfab, pfa], hyps, conc)

def 

def weaken(pfa, newhyp):
    return Proof([pfa], pfa.hyps + [newhyp], pfa.conc)

def swap(pf, i,j):
    return Proof(pf ,pf.hyps, pf.conc)



```
