---
title: Subterms Modulo Theories I
date: 2026-01-19
---

Terms are nice (trees with ordered children). They make sense You can do rewriting on them, unification (equation solving) and (unfailing) completion (equational search). They are at least a relative of egraphs.

Terms are also kind of limiting. There are other things that are term like that we want to generalize these operations to. We want binding forms, baked in symmetries (AC), infinite processes (Rational Terms). These are useful features for modelling problems.

If we want to generalize the lines of how we can deal with regular terms it makes sense to consider the following questions:

1. Can we implement/define equality?
2. What even is the subterm relationship?
3. A notion of context?
4. A notion of pattern matching?
5. A notion of unification? <https://www.philipzucker.com/unify/>
6. A notion of ground term ordering?
7. A notion of ground completion? <https://www.philipzucker.com/egraph2024_talk_done/>
8. How to structurally canonize <https://www.philipzucker.com/pldi_2025/>
9. How to index / fingerprint / hash <https://www.philipzucker.com/hashing-modulo/>

I think that too often people leap to the hard problems of 4 and 5.

1 and 2 are sound easy, and they mostly are. But they aren't _that_ easy.

The problems that are mostly easy but not actually that easy are the best ones to attack. So today, let's investigate how to this this on some term generalizations.

1. Standard Terms
2. AC Terms
3. Closed Terms mod Alpha
4. Open Terms mod renaming

## Standard Terms

"Standard" Terms have ordered children. This makes comparing them by zipping their children easy. The built in notions of equality in python for tuples, etc follow this already. I do sometimes wonder if there is a chicken and egg problem of what available programming languages make easy and the dominance of standard terms.

```python
from dataclasses import dataclass, field
from enum import Enum

@dataclass(frozen=True, order=True)
class App():
    f : str
    args : tuple["App", ...] = ()

def is_eq(t : App, s : App) -> bool:
    if t.f != s.f or len(t.args) != len(s.args):
        return False
    return all(is_eq(a1, a2) for a1, a2 in zip(t.args, s.args))

def is_subterm(t : App, s : App) -> bool:
    if is_eq(t,s):
        return True
    else:
        return any(is_subterm(a, s) for a in t.args)

x = App("x")
y = App("y")
f = lambda x: App("f", (x,))
g = lambda x,y: App("g", (x,y))

assert is_eq(f(x), f(x))
assert is_subterm(f(x), x)
assert not is_eq(f(x), f(y))
assert not is_subterm(f(x), y)
assert not is_subterm(x ,f(x))
```

It is easy to define a ground knuth bendix ordering <https://www.philipzucker.com/ground_kbo/>

```python
def size(t : App) -> int:
    return 1 + sum(size(a) for a in t.args)

class Order(Enum):
    LT = -1
    EQ = 0
    GT = 1

def ground_kbo(t : App, s : App) -> Order:
    if size(t) < size(s):
        return Order.LT
    elif size(t) > size(s):
        return Order.GT
    else:
        if (t.f, len(t.args)) < (s.f, len(s.args)):
            return Order.LT
        elif (t.f, len(t.args)) > (s.f, len(s.args)):
            return Order.GT
        else:
            for a1, a2 in zip(t.args, s.args):
                o = ground_kbo(a1, a2)
                if o != Order.EQ:
                    return o
            return Order.EQ

ground_kbo(f(x), x)
ground_kbo(x,y)
ground_kbo(y,x)
assert ground_kbo(g(x,x), g(x,y)) == ground_kbo(x,y)
assert ground_kbo(g(x,y), g(x,x)) == ground_kbo(y,x)
```

An interesting notion of that of a position inside a term. It is a list of integers describing which hcild you needded to go down to the current position. It is related to the notion of a context (given a position and the term, you can derive a context/zipper <https://en.wikipedia.org/wiki/Zipper_(data_structure)> ).

We sometimes want all positions a term appears in another. This is useful for computing critical pairs for example.

```python
# position
type Pos = tuple[int, ...]

def find_subterm(t : App, s : App) -> list[Pos]:
    res = []
    todo = [((), t)]
    while todo:
        pos, t = todo.pop()
        if is_eq(t,s):
            res.append(pos)
        for i, a in enumerate(t.args):
            todo.append((pos + (i,), a))
    return res

x = App("x")
y = App("y")
f = lambda x: App("f", (x,))
g = lambda x,y: App("g", (x,y))

assert is_eq(f(x), f(x))
assert is_subterm(f(x), x)
assert not is_subterm(x, f(x))
assert not is_subterm(f(x), g(x,y))

find_subterm(g(x,f(x)), f(x))
```

    [(1,)]

## Associative and Commutative (AC)

The basic questions about AC terms are not really that complicated, there is just some search in there. Doing it _well_ might be complicated.

```python

@dataclass(frozen=True)
class ACApp():
    f : str
    args : tuple["ACTerm"]

type ACTerm = App | ACApp

def rec_key(t : ACTerm):
    # an unprincipled, but unique key to use for ordering
    match t:
        case App(f, args):
            return (0, f, tuple(rec_key(a) for a in args))
        case ACApp(f, args):
            return (1, f, tuple(rec_key(a) for a in args))
        case _:
            raise ValueError("Invalid ACTerm", t )

def ac_norm(t : ACTerm) -> ACTerm:
    # recursively flatten and sort
    match t:
        case App(f, args):
            return App(f, tuple(ac_norm(a) for a in args))
        case ACApp(f, args):
            args = [ac_norm(a) for a in args]
            ac = [c for a in args if isinstance(a, ACApp) and a.f == f for c in a.args]
            nonac = [a for a in args if not (isinstance(a, ACApp) and a.f == f)]
            allargs = ac + nonac
            allargs.sort(key=rec_key)
            return ACApp(f, tuple(allargs))
        case _:
            raise ValueError("Invalid ACTerm", t)

add = lambda *args: ACApp("add", args)
mul = lambda *args: ACApp("mul", args)

ac_norm(add(add(add(x)), add(x,y,x,y),x))

```

    ACApp(f='add', args=(App(f='x', args=()), App(f='x', args=()), App(f='x', args=()), App(f='x', args=()), App(f='y', args=()), App(f='y', args=())))

```python
def is_eq(t : ACTerm, s : ACTerm) -> bool:
    return ac_norm(t) == ac_norm(s)

"""
# You can be more efficient by intertwining cheaper equality checks and normalizing
def is_eq(t : ACTerm, s : ACTerm) -> bool:
    if isinstance(t, App) and isinstance(s, App):
        if t.f != s.f or len(t.args) != len(s.args):
            return False
        return all(is_eq(a1, a2) for a1, a2 in zip(t.args, s.args))
    elif isinstance(t, ACApp) and isinstance(s, ACApp):
        # do search. Blegh
        ...
"""

assert is_eq(add(x,y,x), add(y,x,x))
assert not is_eq(add(x,y), add(y,x,x))
assert is_eq(mul(add(x,y), x), mul(x, add(y,x)))

```

```python
import itertools

def is_subterm_app(t : ACTerm, s : App) -> bool:
    # a lot of commoniality between these two. Could refactor back together
    todo = [t]
    while todo:
        t = todo.pop()
        if is_eq(t,s):
            return True
        else:
            match t:
                case App(f, args):
                    todo.extend(args)
                case ACApp(f, args):
                    todo.extend(args)
    return False

def is_subterm_acapp(t : ACTerm, s : ACApp) -> bool:
    todo = [t]
    f0, args0 = s.f, s.args
    while todo:
        t = todo.pop()
        if is_eq(t,s):
            return True
        else:
            match t:
                case App(f, args):
                    todo.extend(args)
                case ACApp(f, args):
                    #if multiset(args0) in multiset(args): return True
                    todo.extend(args)
                    if f == f0 and len(args) >= len(args0):
                        for args1 in itertools.combinations(args, len(args0)): # overly bad
                            if args1 == args0:
                                return True
    return False


def is_subterm(t : ACTerm, s : ACTerm) -> bool:
    s = ac_norm(s)
    match s:
        case App(f, args):
            return is_subterm_app(t, s)
        case ACApp(f, args):
            return is_subterm_acapp(t, s)

assert is_subterm(add(x, mul(x,y)), mul(y,x))
assert not is_subterm(add(x, mul(x,y)), mul(x,x))
assert is_subterm(add(x,x,y), add(x,x))
assert is_subterm(add(x,x,y), add(x,y))
assert not is_subterm(add(x,y), add(x,x))
assert not is_subterm(add(x,y), mul(x,y))
assert is_subterm(mul(add(x,y), add(y,x,x)), add(x,x))
assert not is_subterm(add(x,y), add(x,x,y))

```

The notion of position is interesting. If we work with AC terms on the nose, we don't have that easy of a way of saying where.

ac_norm could be extended to output a trace of how the normalization proceeded, a proof

```python
# Pos will have to include reordering flatten and perm moves
type Pos = ...
```

```python
# One could use smart constructors to never produce non-normalized ACApps
def smart_ac(f):
    def res(*args):
        # flatten and sort
        flat_args = []
        for a in args:
            if isinstance(a, ACApp) and a.f == f:
                flat_args.extend(a.args)
            else:
                flat_args.append(a)
        flat_args.sort(key=rec_key)
        return ACApp(f, tuple(flat_args))
```

## Alpha

This is the weakest notion of subterm involving binders. In this understanding only closed terms can be equal.

There is something spiritually correct about every time you entering a binder it should be considered a different thing. In this respect, Hash Consing modulo alpha is an incoherent desire. Of course, fast equality checks and reduced memory usage are coherent desires.

Here I do a basic locally nameless style thing. <https://cstheory.stackexchange.com/questions/53104/locally-nameless-representation-implementation>  <https://chargueraud.org/research/2009/ln/main.pdf>

We use de bruijn indices <https://en.wikipedia.org/wiki/De_Bruijn_index> for bound variables and when we traverse under binders, we replace them with fresh free variables. Doing this consistently avoids bad capture.

![](https://en.wikipedia.org/wiki/File:De_Bruijn_index_illustration_1.svg)

De Bruijn indices refer to their binder by the number of binders they have to traverse to get to it. This makes sense from the perspective that the interpretation of each binder is pushing something onto some kind of stack.

```python
# Bound de bruijn variables
@dataclass(frozen=True)
class BVar():
    idx : int

# Free variables
@dataclass(frozen=True)
class FVar():
    name : str

# Binder. One might call this "Lam", but I don't want to imply lambda calculus
@dataclass(frozen=True)
class Bind():
    # would be fun to overload __match_args__ to use open_binder?
    body : "OpenTerm"

# Note that my App is not binary lambda application. It's full n-ary application of a function symbol

type ClosedTerm = BVar | App | Bind
type OpenTerm = ClosedTerm | FVar

def bind(v : str, body : OpenTerm) -> OpenTerm:
    # smart constructor for Bind
    return Bind(close(body, v, 0))

def close(t : OpenTerm, v : str, idx : int):
    # turn free variable v into bvar(idx). Bump idx when traversing under a new binder
    match t:
        case FVar(n):
            if n == v:
                return BVar(idx)
            else:
                return t
        case App(f, args):
            return App(f, tuple(close(a, v, idx) for a in args))
        case Bind(body):
            return Bind(close(body, v, idx + 1))
        case BVar(_):
            return t
        case _:
            raise ValueError(f"Unknown term type: {t}")


counter = 0
def fresh() -> FVar:
    global counter
    counter += 1
    return FVar(f"_x{counter}")

a = FVar("a")
b = FVar("b")
bind("b", bind("a", g(a,b)))


def is_closed(t : OpenTerm) -> bool:
    # no free variables
    match t:
        case FVar(_):
            return False
        case App(f, args):
            return all(is_closed(a) for a in args)
        case Bind(body):
            return is_closed(body)
        case BVar(_):
            return True
        case _:
            raise ValueError(f"Unknown term type: {t}")


def subst_bvar(t : OpenTerm, idx : int, e : OpenTerm) -> OpenTerm:
    # turn any bvar(idx) into e. Bump idx when traversing under a new binder
    # Not correct if you haven't been following locally nameless discipline
    match t:
        case FVar(_):
            return t
        case BVar(i):
            if i == idx:
                return e
            else:
                return t
        case App(f, args):
            return App(f, tuple(subst_bvar(a, idx, e) for a in args))
        case Bind(body):
            return Bind(subst_bvar(body, idx + 1, e))
        case _:
            raise ValueError(f"Unknown term type: {t}")

def open_binder(b : Bind) -> tuple[FVar, OpenTerm]:
    # To open a binder, replace the associated bvars with a fresh fvar
    assert isinstance(b, Bind)
    v = fresh()
    body = subst_bvar(b.body, 0, v)
    return FVar, body
```

The magic of the de Bruijn representation is that closed alpha equivalent terms are structurally equivalent.

```python
def is_eq(t : ClosedTerm, s : ClosedTerm) -> bool:
    assert is_closed(t) and is_closed(s)
    return t == s # just proceed strucutrally
```

`is_subterm` is unchanged except that you `open_binder` at a binder node. This means we'll never have a captured variable escape its context.

```python
def is_subterm(t : ClosedTerm, s : ClosedTerm) -> bool:
    assert is_closed(t) and is_closed(s)
    # assert is_closed(s) just s has to be closed ?
    if is_eq(t,s):
        return True
    match t:
        case App(f, args):
            return any(is_subterm(a, s) for a in args)
        case Bind(_):
            v, body = open_binder(t) # Note the need to open here.
            return is_subterm(body, s)
        case BVar(_):
            return False
        case _:
            raise ValueError(f"Unknown term type: {t}")

```

```python
type Pos = tuple[int, ...] 

def find_subterms(t : ClosedTerm, s : ClosedTerm) -> list[Pos]:
    assert is_closed(t) and is_closed(s)
    res = []
    todo = [((), t)]
    while todo:
        pos, t = todo.pop()
        if is_eq(t,s):
            res.append(pos)
        match t:
            case App(f, args):
                for i, a in enumerate(args):
                    todo.append((pos + (i,), a))
            case Bind(_):
                v, body = open_binder(t)
                todo.append((pos + (0,), body))
            case BVar(_):
                pass
            case _:
                raise ValueError(f"Unknown term type: {t}")
    return res
```

This is a pretty weak notion of subterm. There is a more expressive thing we can do

## Miller / Nominal / Slotted / AC Alpha

Another thing we can do though instead of requiring terms be closed is to see if there is some permutative renaming of the free variables that could make the terms equal.

The "Miller" notion of a term I have also seen called matching modulo $\beta_0$. The idea here is that only $\beta_0$ substitutions are considered rather than full $\beta$ substitution. $\beta_0$ performs substitution but only when a lambda is applied to unique free variables and nothing else. Using this move, we can insert a binder at any position to make the subterm closed in the appropriate sense. For example, in the following example we can find a way to insert a $\beta_0$ move in order to find a subterm where we did not before

```
is_subterm(bind(f(bvar(0), fvar(a))), 
           bind(bind(f(bvar(0), bvar(1)))))

---> beta_0

is_subterm(bind(bind(f(bvar(0), bvar(1))))(fvar(a)), 
           bind(bind(f(bvar(0), bvar(1)))))

--->

true

```

I think it is more conceptually clear to not think of this as related to the lambda calculus at all. It also appears to me that n-arity application makes the subject more clean than trying to reduce it to binary application. I described a version of this here <https://www.philipzucker.com/ho_unify/> . I used an Ocaml datatype that looks like

```ocaml
type term_miller = 
    | Binder of term_pat (* binder represented as de Bruijn *)
    | BVar of int
    | Const of string * term_pat list
```

This is to some degree a strange merging of the notion of AC and Bind. There is a binder at play that is multiarity and unordered. Implicit binders (like einstein notation or prolog variables) are like that.

If one has 2 free variables, there are at least two ways to $\beta_0$ expand at the top level.

```
bind(bind(g(bvar(0), bvar(1)))(fbar(a)))(fvar(b))   <-- g(fvar(a), fvar(b)) --->  bind(bind(g(bvar(1), bvar(0)))(fbar(b)))(fvar(a))
```

So perhaps it is useful to think of this as an AC binder

```
g(fvar(a), fvar(b)) ~ acbind({a,b}, g(fvar(a), fvar(b)))
```

To implement equality, we can tracked a renaming. Discovering the renaming looks rather similar to implementing regular term unification, except for the condition that the renaming should fail if we try to bind it twice.

What I've described here isn't exactly Miller patterns or nominal or slotted matching <https://dl.acm.org/doi/10.1145/3729326> , but I think it's in the ballpark of all of them. The plan is roughly to use this version of term in a version of ground completion to get something like a slotted egraph

```python
from dataclasses import dataclass, field
from typing import Optional

@dataclass
class Rename():
    # A permutative renaming between free variables
    ab : dict = field(default_factory=dict)
    ba : dict = field(default_factory=dict)
    def add(self, a, b):
        if a in self.ab:
            return self.ab[a] == b
        elif b in self.ba:
            return self.ba[b] == a
        else:
            self.ab[a] = b
            self.ba[b] = a
            return True

def is_eq(t : OpenTerm, s : OpenTerm) -> Optional[Rename]:
    rename = Rename()
    todo = [(t, s)]
    while todo:
        t, s = todo.pop()
        match t, s:
            case FVar(n1), FVar(n2):
                if not rename.add(n1, n2):
                    return None
            case BVar(i1), BVar(i2):
                if i1 != i2:
                    return None
            case App(f1, args1), App(f2, args2):
                if f1 != f2 or len(args1) != len(args2):
                    return None
                todo.extend(zip(args1, args2))
            case Bind(body1), Bind(body2):
                v1, body1 = open_binder(t)
                v2, body2 = open_binder(s)
                if not rename.add(v1.name, v2.name):
                    return None
                todo.append((body1, body2))
            case _:
                return None
    return rename

is_eq(f(a), f(b))
```

    Rename(ab={'a': 'b'}, ba={'b': 'a'})

```python
is_eq(f(x), f(x))
```

    Rename(ab={}, ba={})

```python
is_eq(g(a,a), g(b,b))
```

    Rename(ab={'a': 'b'}, ba={'b': 'a'})

```python
assert is_eq(g(a,b), g(a,a)) is None
```

The subterm relationship like before uses `is_eq`. It still opens binders. But now it is possible for terms to match that have open variables.

```python
def is_subterm(t : OpenTerm, s : OpenTerm) -> bool:
    todo = [t]
    while todo:
        t = todo.pop()
        if is_eq(t,s) is not None:
            return True
        match t:
            case FVar(_):
                pass
            case BVar(_):
                pass
            case App(f, args):
                todo.extend(args)
            case Bind(body):
                v, body = open_binder(t)
                todo.append(body)
            case _:
                raise ValueError(f"Unknown term type: {t}")
    return False
```

We have kind of left implicit how many free variables are floating around in the term. There are at least the number of free vars in there

```python
def free_vars(t : OpenTerm) -> set[FVar]:
    res = set()
    todo = [t]
    while todo:
        t = todo.pop()
        match t:
            case FVar(n):
                res.add(t)
            case BVar(_):
                continue
            case App(f, args):
                todo.extend(args)
            case Bind(body):
                todo.append(body)
            case _:
                raise ValueError(f"Unknown term type: {t}")
```

But there may be bound stuff we just didn't use in some sense. Whether this distinction is useful or not is unclear. But to note a superset of the fvars in the term, we may want to introduce the notion of an `ACBind`

```python
@dataclass(frozen=True)
class ACBind():
    vs : frozenset[FVar]
    body : OpenTerm

    def eq(self, other : "ACBind") -> Rename:
        return is_eq(self.vs, self.body, other.vs, other.body)

```

# Bits and Bobbles

I want to do generalized ground completion. I don't feel like I have nailed what the miller thing is exactly.
I also need notions of term ordering.
<https://courses.grainger.illinois.edu/cs576/sp2017/readings/18-mar-9/rubio-ac-rpo-long.pdf> AC-RPO
<https://arxiv.org/abs/1403.0406> AC-KBO

Some things can't be ordered. Need unfailing ground completion (A contradictory concept until you start considering term generalizations). These might correspond to self symetries in slotted (?).

A lot of confusion comes from using the blanket term "lambda" to refer to or model many different kinds of syntactic binding.

Lambda has a connotation of full beta substitution, which _the original purpose of_ was to model the general notion of algorithm (Turing completeness). From this standpoint, we should expect asking even simple questions of such a thing to be disastrous.

The situation is spiritually analogous to that of regex, pushdown automata, and turning machines. Many things are tractable in the weaker systems, which can inform methods for treating the more powerful but difficult systems.

You can ask very nasty questions like about general graphs, where it is not clear that these pieces make sense.

Abstract rewriting and abstract completion does not mention the term structure. They call them `t` and `s` and your mind thinks "term", but the notion of application does not show up anywhere.

In order to have generalized ground completion / generalized congruence closure / generalized egraph, you only need

1. finding subterms for critical pair finding
2. a ground term ordering (?)

The typical thinking about egraphs does not include an a priori term ordering. Since term orderings are confusing and suck, is this true in general?

1. Closed Alpha Equivalent Terms
2. Rational
3. AC
4. Miller / Nominal / slotted / Permutation equivalence. "AC Alpha"
5. Polynomials
6. LFHOL - allowing binary app and compound expressions in the function position.

## Rational Terms

```python
from dataclasses import dataclass, field
# not frozen, because we need to tie knots
@dataclass
class App():
    f: str
    args: list = field(default_factory=list)


def is_eq(t : App, s : App, table : frozenset[tuple[int, int]]=frozenset()):
    if (id(t), id(s)) in table:
        return True
    if t.f != s.f or len(t.args) != len(s.args):
        return False
    table |= {(id(t), id(s))}
    return all(is_eq(ta,sa, table) for ta, sa in zip(t.args, s.args))

def f(*args):
    return App("f", list(args))
finf = f()
finf.args = [finf]
x = App("x", [])
assert is_eq(f0, f0)
is_eq(f(x), finf)

finf2 = f(finf)
assert is_eq(finf2, finf)
assert not is_eq(finf2, f(x))

finf0 = f()
finf3 = f(f(finf0))
finf0.args = [finf3]

assert is_eq(finf0, finf3)
assert is_eq(finf2, finf3)
finf3
```

## Polynomials

```python
type R = int # other concrete coefficient types / rings could work

@dataclass
class PolyApp():
    add : str # There may be multiple notions of addition and multiplication.
    mul : str
    terms : tuple[tuple[R, tuple[Terms]]] # a sum of products



```

## Dict Terms

Despite the unordered character of the keyword arguments, this much closer to being akin to regular App than it is to being ACApp. That's kind of interesting.

The notion of subterm can include ignoring some of the arugments.

Reasonable notions of pattern can include record patterns, which capure all the other arguments. This gives somewhat a solution to the frame problem.

If the keys of the kwargs are allowed to be other terms, then perhaps we're getting into alias issues. Separation logic, etc.

```python
class KWApp():
    f : str
    args : tuple[KWApp, ...] # ordered args
    optargs : tuple[Optional[KWApp], ...] # optional args
    kwargs : dict[str, KWApp] # keyword args
```

```python
class 
```

```python


#def extend_perm(p, a, b): ...


```

```python
from dataclasses import dataclass, field
@dataclass
class Rename():
    ab : dict = field(default_factory=dict)
    ba : dict = field(default_factory=dict)
    def add(self, a, b):
        if a in self.ab:
            if not self.ab[a].eq(b):
                raise ValueError(f"Conflict in renaming: {a} -> {self.ab[a]} vs {a} -> {b}")
        elif b in self.ba:
            if not self.ba[b].eq(a):
                raise ValueError(f"Conflict in renaming: {self.ba[b]} -> {b} vs {a} -> {b}")
        else:
            self.ab[a] = b
            self.ba[b] = a

```

```python
from kdrag.all import *


def perm_eq(vs1, t1, vs2, t2):
    todo = [(t1,t2)]
    rename = Rename()
    while todo:
        t1, t2 = todo.pop()
        if t1.eq(t2):
            continue
        if smt.is_const(t1) and smt.is_const(t2):
            is_fvar1 = any(t1.eq(v) for v in vs1)
            is_fvar2 = any(t2.eq(v) for v in vs2)
            #print(f"Comparing constants {t1}, {t2}: is_fvar1={is_fvar1}, is_fvar2={is_fvar2}")
            if is_fvar1 != is_fvar2: # one is free var, one is const
                return None
            elif is_fvar1 and is_fvar2: # both free vars
                try:
                    rename.add(t1, t2)
                except ValueError:
                    return None
            elif not t1.eq(t2): # both constants not equal
                    return None
        elif smt.is_app(t1) and smt.is_app(t2):
            if t1.num_args() != t2.num_args() or t1.decl() != t2.decl():
                #print("Mismatch in number of args or decls", t1.decl(), t2.decl())
                return None
            todo.extend(zip(t1.children(), t2.children()))
        elif isinstance(t1, smt.QuantifierRef) and isinstance(t2, smt.QuantifierRef):
            if t1.num_vars() != t2.num_vars():
                return None
            if t1.is_forall() == t2.is_forall() or t1.is_exists() == t2.is_exists() or t1.is_lambda() == t2.is_lambda():
                vs, b1 = kd.utils.open_binder(t1)
                b2 = smt.substitute_vars(t2.body(), *vs)
                todo.append((b1, b2))
    return rename


x,y,z = smt.Ints("x y z")
x1,y1 = smt.Ints("x1 y1")
assert perm_eq([], x,[], y) is None
assert perm_eq([x], x, [y], y) is not None
assert perm_eq([x,y], x + x, [x1,y1], y1 + y1) is not None
assert perm_eq([x,y], x + x, [x1,y1], x1 + y1) is None
assert perm_eq([x,y], x + y, [x1,y1], y1 + x1) is not None
assert perm_eq([x,y], smt.ForAll([x], x > 1), [y1], smt.ForAll([y1], y1 > 1)) is not None
assert perm_eq([])

```

is_subterm can be implemented fairlyu generically using a notion of equality.

Like rational terms.

```python
def issubterms(vs1, t1, vs2, t2):
    todo = [t2]
    res = []
    while todo:
        t = todo.pop()
        r = perm_eq(vs1, t1, vs2, t)
        if r is not None:
            return r # and maybe subposition?
            # hmm. the rename is useless as is?
            # uhh not necessarily
        if smt.is_app(t):
            todo.extend(t.children())
        elif isinstance(t, smt.QuantifierRef):
            vs, body = kd.utils.open_binder(t)
            vs1.extend(vs)
            todo.append(body)
    return None
```

```python
def subterms(vs1, t1, vs2, t2):
    todo = [((), t2)]
    res = []
    while todo:
        pos, t = todo.pop()
        r = perm_eq(vs1, t1, vs2, t)
        if r is not None:
            res.append((pos, r))
            continue # we won't find t2 as a smaller subterm
        elif smt.is_app(t):
            todo.extend((pos + (i,), c) for i,c in enumerate(t.children()))
        elif isinstance(t, smt.QuantifierRef):
            vs, body = kd.utils.open_binder(t)
            vs1.extend(vs)
            todo.append((pos + (0,), body))
    return res


```

```python
@dataclass
class OpenTerm():
    vs : set[smt.ExprRef] # set, not list.
    t : smt.ExprRef


```

```python
def beta0_norm(vs, t):
    if smt.is_app(t):
        children = t.children()
        if smt.is_select(t) and all(any(c.eq(v) for v in vs) for c in children[1:]) and len(set(c.get_id() for c in children[1:])) == len(children[1:]):
            # do beta0
            ...
        else:
            return t.decl()(*[c.beta0_norm(vs, c) for c in t.children()])
    elif isinstance(t, smt.QuantifierRef):
        vs1, body = kd.utils.open_binder(t)
        body_norm = beta0_norm(vs + vs1, body)
        if t.is_forall():
            return smt.ForAll(vs1, body_norm)
        elif t.is_exists():
            return smt.Exists(vs1, body_norm)
        elif t.is_lambda():
            return smt.Lambda(vs1, body_norm)


```

```python
type Id = usize;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Node {
    App(Id,Id),
    Lam(Id),
    Var(usize),
}

#[derive(Debug, Clone)]
struct TermBank {
    terms: Vec<Node>,
    memo : HashMap<Node, Id>
}
```

Cody cast suspicion that miller subterms was actually easy

```python

class App():

class Var():

class 


# or do z3


```

mu {x,y,z}. lam lam lam

need examples.
go insidie and find de bruijn permutation
beta0 normalize

So the suggested idea is that
