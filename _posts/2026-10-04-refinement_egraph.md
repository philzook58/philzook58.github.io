---
title: Refinement E-Graphs
date: 2026-10-04
---

The idea of a refinement [e-graph](https://egraphs.org/) is to add a baked in a `<=` relation that is about as privileged as the e-graph's native `=`

There is a story that compiler rewrites are often not bidirectional equalities, but instead are unidirectional refinement rewrites, moving from an abstract or floppy program / spec to a more completely determined one that can run on a concrete machine. It is quite common for the source language to be cagey about the exact order the children of an expression are evaluated, or what is the result of an integer overflow or division by zero. Being cagey may enable more optimization opportunities or ease translation to disparate machines. It is also just a fact of life for these languages.

Here is a prototype <https://github.com/philzook58/refinement-microegg> of a refinement egraph based on Max Willsey's microegg <https://github.com/mwillsey/microegg>. A WASM demo is here <https://www.philipzucker.com/refinement-microegg>. Third verse same as the [second](https://www.philipzucker.com/lambda_miller_egg/)

# Example: Don't Care Circuits

A nice example is "Don't Care" in digital circuits <https://en.wikipedia.org/wiki/Don%27t-care_term> , You may say that certain inputs are not supported to a circuit and that the result is a don't care in that case. An optimizer is free to pick a result that allows for the most optimal circuit. I believe George Constantinides explained a version of this example to me.

```python
%%file /tmp/circuit.sexp
(fun ite (+ + +)) ; declare if-then-else as covariant in all arguments
(rewrite (ite ?x true false) ?x)  ; ordinary equality rewrite
(ge dontcare true)    ; dontcare refines to true. {True, False} >= {True}
(ge dontcare false)   ; dontcare also refines to false. {True, False} >= {False}

(insert (ite x true dontcare)) ; insert starting term
(run 5 :expand-le)

(extract-le (ite x true dontcare))  ; can extract x because refining this dontcare to true enables a nice term
```

    Writing /tmp/circuit.sexp

```python
! refinement-microegg /tmp/circuit.sexp
```

    x

There are also refinement rewrite rules available in the implementation, `rewrite-le` and `rewrite-ge`. 

Spiritually, `(rewrite-le lhs rhs)` represents the formula `forall ?a, lhs(?a) <= rhs(?a)`. Because of the form of this formula, we don't have to match `lhs` on the equality nose. We can find a substitution for any starting `?t <= subst(lhs[?a])` to chain to a discovered inequality assertion `?t <= subst(lhs[?a]) <= subst(rhs[?a])`.

## Don't Care Semantics

I think semantics is really important and don't like meaningless syntax manipulation. The intended semantics of this "Don't Care" example is `Bool -> Set Bool` with `<=` representing pointwise set containment.

| Term         | Semantics                                                                       |
| ------------ | ------------------------------------------------------------------------------- |
| `x`          | `fun b => {b}`                                                                  |
| `ite(c,t,e)` | `fun b => {res for c1 in [[c]] b for res in (if c1 then [[t]] b else [[e]] b)}` |
| `dontcare`   | `fun _ => {True, False}`                                                        |
| `true`       | `fun _ => {True}`                                                               |
| `false`      | `fun _ => {False}`                                                              |
| `t <= s`     | `forall b : Bool, is_subset ([[t]] b) ([[s]] b)`                                |

`x` could be generalized to have an algebra of more than one dimension, which would bring us back to lifting e-graphs <https://www.philipzucker.com/lambda_miller_egg/> <https://www.youtube.com/watch?v=h1CzZguA6DE> . Refinement and Lambda afaik are orthogonal features that have no issue being bolted together. Maybe something interesting might occur in extraction (some related terms may not exist in some contexts)?

Note that this inequality assertion is distinct from _equating_ `dontcare = true = false`. This of course is problematic. But it is also distinct from equating to either of them `dontcare = true` or `dontcare = false`. If we did one of these, then all `dontcare` _everywhere_ would be forced to be `true` or `false`, whereas we want the ability to be able to make independent choices at all usages.
One could perhaps make `dontcare1` `dontcare2` `dontcare3` etc as fresh constants and then independently equate them. This freshness game always feels like some goofy shell game to me though.
There is some intuitive sense that equating an eclass destroys it as a resource, but stating an inequality does not destroy it as a resource. This is good and bad. "Destroying" is a similar thing to compaction and canonization. The inequality isn't operationally as nice as the "destroying" equality.

# Inequality Union Finds

Roughly E-Graph = Union Find + Hash Cons. So a Refinement E-graph = inequality union find + hash cons.

The interface of the inequality union find is more important than the details of the implementation.

```python
from typing import Protocol
type Id = int
class LE_UnionFind(Protocol):
    # regular union find
    def union(self, a : Id, b : Id) -> None: ...
    def is_eq(self, a : Id, b : Id) -> bool: ...
    def find(self, a : Id) -> Id: ...

    # extra inequality features
    def add_le(self, a : Id, b : Id) -> None: ... # the analog of union. union = add_eq
    def is_le(self, a : Id, b : Id) -> bool: ...# analog of is_eq
    def all_le(self, a : Id) -> set[Id]: ... # returns all elements `a` is known less than or equal to. Analog of find.
    def all_ge(self, a : Id) -> set[Id]: ... # returns all elements known `a` is known greater than or equal to. Analog of find.

```

Previous discussions of mine on inequality union finds towards refinement e-graphs:

- <https://www.philipzucker.com/asymmetric_complete/> An Inequality Union Find Inspired by Atomic Asymmetric Completion
- <https://www.philipzucker.com/le_find/> Inequality Union Finds: Baby Steps to Refinement E-graphs

# What Does A Refinement E-Graph Need on Top of This?

An (inequality) union find deals in atomic symbols `e4` and atomic equations `e5 = e87` (or inequations `e4 <= e65`).

An e-graph adds function symbols `f(e4,e4)` to this. These symbols appear in the following processes:

- Refinement-closure
- Refinement E-matching
- Refinement extraction

The e-graph implementation need to be told how the function symbols play with the inequality `<=` by the user. Functions _always_ respect equality `=`, but they may be monotone, anti-monotone or neither/unknown in their individual arguments. I like set difference `diff(A,B)` as an example of this. It is monotone in the first argument but anti-monotone/contravariant in the second argument `diff(+,-)`.

## Refinement Closure

Instead of congruence closure, we can perform refinement closure. This basically is applying a theorems like `forall a b c d, a <= b /\ c >= d -> diff(a,c) <= diff(b,d)` instead of `a = b /\ c = d -> diff(a,c) = diff(b, d)` which is what congruence closure applies.

Refinement closure isn't as nice as congruence closure. We can use it both in the form that makes new enodes or the form that only notes relations between pre-existing enodes. In a datalog sense, this is the difference between
`diff(a,c) <= diff(b,d) :- a <= b, c >= d, diff(a,c)` and the guarded version `diff(a,c) <= diff(b,d) :- a <= b, c >= d, diff(a,c), diff(b,d)`. The first can be useful, but it can also be explosive.

## Refinement E-matching

Pattern matching can be modelled as a processing a constraint set `{?p = t}` (see for example section 2.2.3 of https://www.cs.bu.edu/fac/snyder/publications/UnifChapter.pdf or section 4.6 of Term Rewriting and All That ). What makes it pattern matching vs unification is having variable only on one side, which is sometimes easier/more efficient to implement.

![unification rules](https://www.philipzucker.com/assets/traat/unify_rules.png)

For refinement e-matching, We can be working with a constraint `{?p <= t}` or `{t <= ?p}`. But otherwise really the algorithm doesn't change that much. You just need to track which "mode" you're currently in, and change the mode according to the variance of the function symbols.

For example, this `diff` pattern processes by flipping one of the modes.`{diff(?a, ?b) <= diff(x,y)}  ===>  {?a <= x, ?b >= y}`

In the implementation, there is one extra degree of nondeterminism on top of the usual e-matching eclass->enode nondeterminsm, where in the `GE` or `LE` mode, you may traverse an eclass -> eclass `<=` edge. 

From the flattened relational e-matching perspective, this is the insertion of implicit `(le ?a ?b)` all throughout the pattern. For example  the pattern`foo(bar(?x))` becomes flattened to `?e1 = foo(?e2), ?e2 <= ?e3, ?e3 = bar(?e4), ?e4 <= ?x`. `<=` kind of "mediates" between every function symbol relation.

## Refinement Extraction

Regular extraction is actually pretty similar to e-matching in many ways. We are seeking a `?extract = t` but we want the "best" `?extract`. We have a tendency to implement extraction bottom up instead of top down.  

In refinement extraction, we can instead be asking for `?extract <= t` or `?extract >= t`. We might also want to use `<=` in our definition of "best". Perhaps we want the most refined (which semantically might mean the most concretely implemented or most deterministic entity) and then tie break with smallest size term or vice versa.

# A Toy Python Implementation of a Refinement E-Graph

This is basically a copy of my python microegg with some inequality smarts put in. There is a refinement closure step `le_cong_step` and `le_cong_step_weak` (which makes no new enodes). Because e-matching can traverse `<=` edges, you might need less materialization than you'd think.

ematching and extraction are keyed on `Mode` which says whether you are allowed to search up or down the `<=` or have to use on the nose `=`.

The variance table `variance : dict[str, tuple[Variance, ...]]` says the variance of each argument of the function symbol. It is kind of the same shape of data one might use for storying types of the symbols, but this implementation is untyped.

```python
from dataclasses import dataclass, field
from enum import Enum
from collections import defaultdict
import itertools
type Id = int
@dataclass(frozen=True)
class Node:
    f : str
    children : tuple[Id,...]

class Mode(Enum): # Expand all below, all above, or equal only. Ematch, extract, and rebuild can all be keyed on this kind of
    LE = -1
    EQ = 0 # Only Eq
    GE = 1
    # Both = 2. I guess since equalitt rewrites can chain with either <= or >=, we could have a BOTH mode

class Variance(Enum): # Slash Monotonicity
    MONO = 1    # covariant
    ANTI = -1   # contravariant
    UNKNOWN = 0 # "invariant"
    #COVARIANT = 1   # monotone
    #CONTRAVARIANT = -1 # antitone
    #INVARIANT = 0   # neither monotone nor antitone
    def act(self, mode: Mode) -> Mode:
        match self:
            case Variance.MONO:
                return mode
            case Variance.ANTI:
                return Mode(-mode.value)
            case Variance.UNKNOWN:
                return Mode.EQ

class Term: ...
@dataclass
class App(Term):
    f : str
    children : tuple[Term,...]
    def size(self) -> int: # used in extraction
        return 1 + sum(child.size() for child in self.children)
@dataclass 
class Var(Term):
    name : str

type Subst = dict[str, Id]

@dataclass
class LE_EGraph():
    parents : list[Id] = field(default_factory=list)
    memo : dict[Node, Id] = field(default_factory=dict)
    uppers : list[set[Id]] = field(default_factory=list)
    lowers : list[set[Id]] = field(default_factory=list)
    variance : dict[str, tuple[Variance, ...]] = field(default_factory=dict)

    def get_variance(self, f: str, arity: int) -> tuple[Variance, ...]:
        sig = self.variance.get(f, (Variance.UNKNOWN,) * arity)
        assert len(sig) == arity
        return sig

    def find(self, a : Id) -> Id:
        while self.parents[a] != a:
            a = self.parents[a]
        return a
    def union(self, a : Id, b : Id) -> None:
        a,b = self.find(a), self.find(b)
        if a == b:
            return
        self.parents[b] = a
        self.uppers[a] |= self.uppers[b]
        self.lowers[a] |= self.lowers[b]
    def add(self, f, *args : Id) -> Id:
        args = tuple(self.find(a) for a in args)
        node = Node(f, args)
        if node in self.memo:
            return self.find(self.memo[node])
        new_id = len(self.parents)
        self.parents.append(new_id)
        self.uppers.append(set())
        self.lowers.append(set())
        self.memo[node] = new_id
        return new_id
    def is_eq(self, a : Id, b : Id) -> bool:
        return self.find(a) == self.find(b)
    def all_le(self, a : Id) -> set[Id]:
        a = self.find(a)
        u = {self.find(x) for x in self.uppers[a]}
        u.add(a) # reflexive
        todo = list(u)
        while todo:
            x = self.find(todo.pop())
            for y in self.uppers[x]:
                y = self.find(y)
                if y not in u:
                    u.add(y)
                    todo.append(y)
        return u
    def all_ge(self, a : Id) -> set[Id]:
        a = self.find(a)
        l = {self.find(x) for x in self.lowers[a]}
        l.add(a) # reflexive
        todo = list(l)
        while todo:
            x = self.find(todo.pop())
            for y in self.lowers[x]:
                y = self.find(y)
                if y not in l:
                    l.add(y)
                    todo.append(y)
        return l
    def add_le(self, a : Id, b : Id) -> None:
        a,b = self.find(a), self.find(b)
        if a == b:
            return
        self.uppers[a].add(b) # could not do so if already found. Help keep uppers sparse
        self.lowers[b].add(a)
    def is_le(self, a : Id, b : Id) -> bool:
        return self.find(b) in self.all_le(a) # We don't have to collect up all_le to compute this but this is easy
    #def cong_step(self, mode : Mode): ...
    # rebuild is applying eq_cong_step in a loop
    def eq_cong_step(self):
        for node, id in list(self.memo.items()):
            children1 = [self.find(a) for a in node.children]
            if children1 == list(node.children):
                continue
            else:
                del self.memo[node] # It is important for e-matching to remove stale nodes.
                id1 = self.add(node.f, *children1)
                self.union(id, id1) # could pollute union find less by giving a variant of self.add id
    def le_cong_step(self):
        for node, id in list(self.memo.items()):
            children = [self.find(a) for a in node.children]
            id1 = self.add(node.f, *children)
            sig = self.get_variance(node.f, len(node.children))
            for c2 in itertools.product(*[self.expand_eclass(a, v.act(Mode.LE)) for a, v in zip(node.children, sig)]):
                id2 = self.add(node.f, *c2)
                self.add_le(id, id2)
        # It is not obvious that le cong should something stale. It probably shouldn't
    def ge_cong_step(self):
        # Just the opposite directin of le_cong_step
        for node, id in list(self.memo.items()):
            children = [self.find(a) for a in node.children]
            id1 = self.add(node.f, *children)
            sig = self.get_variance(node.f, len(node.children))
            for c2 in itertools.product(*[self.expand_eclass(a, v.act(Mode.GE)) for a, v in zip(node.children, sig)]):
                id2 = self.add(node.f, *c2)
                self.add_le(id2, id)
    def le_cong_weak(self): 
        # Don't make new enodes. But instead set pre-existing enodes as le
        for node,id in self.memo.items():
            sig = self.get_variance(node.f, len(node.children))
            for c2 in itertools.product(*[self.expand_eclass(a, v.act(Mode.LE)) for a, v in zip(node.children, sig)]):
                id2 = self.memo.get(Node(node.f, c2))
                if id2 is not None:
                    self.add_le(id, id2)
    def expand_eclass(self, a : Id, mode : Mode) -> set[Id]:
        a = self.find(a)
        if mode == Mode.LE:
            return self.all_le(a)
        elif mode == Mode.GE:
            return self.all_ge(a)
        else:
            return {a}
    def nodes_in_class(self, id: Id, mode : Mode) -> list[Node]:
        ids = self.expand_eclass(id, mode)
        return [obj for obj, obj_id in self.memo.items() if self.find(obj_id) in ids]
    def ematch_rec(self, id : Id, pat : Term, mode : Mode, subst) -> list[Subst]:
        # perhaps expand_eclass should be pulled up here.
        match pat:
            case Var(name): # should allow Var to expand_eclass? Probably. Ok.
                if name in subst:
                    return [subst] if self.find(subst[name]) in self.expand_eclass(id, mode) else []
                else:
                    return [{**subst, name: self.find(id)} for id in self.expand_eclass(id, mode)]
            case App(f, args):
                sig = self.get_variance(f, len(args))
                new_modes = [v.act(mode) for v in sig]
                results = []
                # In this style of doing it, the ONLY change to support refinement is the implementation of nodes_in_class
                for node in self.nodes_in_class(id, mode): # nodes_le_class(id) ?
                    if node.f == f and len(node.children) == len(args):
                        todo = [subst]
                        for arg_pattern, arg_id, arg_mode in zip(args, node.children, new_modes):
                            todo = [
                                subst1
                                for subst0 in todo
                                for subst1 in self.ematch_rec(
                                    arg_id, arg_pattern, arg_mode, subst0
                                )
                            ]
                        results.extend(todo)
                return results
    def extract(self, id : Id, mode : Mode) -> set[Id]:
        # Is this top down extraction busted? Is it actually ok to do the None trick or is it possible visitation order matters?
        memo = {}
        def worker(id: Id, mode : Mode) -> Term:
            id = self.find(id)  # probably redundant
            key = (id, mode)
            if key in memo:
                return memo[key]
            else:
                memo[key] = None  # mark as in progress to avoid infinite loops
                best_cost, best_term = float("inf"), None
                for node in self.nodes_in_class(id, mode):
                    variance = self.get_variance(node.f, len(node.children))

                    args = tuple(worker(arg_id, v.act(mode)) for arg_id, v in zip(node.children, variance))
                    if any(arg is None for arg in args):
                        continue  # subterm hit recursion, skip this node
                    term = App(node.f, args)
                    cost = term.size() + 1 # You don't want to be recursing down terms like this. Should also memoize cost.
                    if cost < best_cost:
                        best_cost, best_term = cost, term
                memo[key] = best_term
                return best_term
        return worker(id, mode)
                

        


    #def rebuild(self) -> None:
    #def ematch(self, mode : Mode): 
    #def extract(self, mode : Mode): 


E = LE_EGraph()
a, b = E.add("a"), E.add("b")
fa, fb = E.add("f", a), E.add("f", b)
E.union(a, b)
assert not E.is_eq(fa, fb)
E.eq_cong_step()
assert E.is_eq(a, b)
assert E.is_eq(fa, fb)



```

```python
E = LE_EGraph()
E.variance["f"] = (Variance.MONO,)
a, b = E.add("a"), E.add("b")
fa, fb = E.add("f", a), E.add("f", b)
E.add_le(a, b)
assert E.is_le(a, b)
assert E.is_le(a, a)
assert not E.is_le(b, a)
E.le_cong_step()
assert E.is_le(fa, fb)

```

```python
E = LE_EGraph()
E.variance["diff"] = (Variance.MONO,Variance.ANTI)
a, b,c,d = E.add("a"), E.add("b"), E.add("c"), E.add("d")
diff_ab = E.add("diff", a, b)
E.add_le(b, c)
E.add_le(c, d)
#E.le_cong_step()
#E.ge_cong_step()
E.ematch_rec(diff_ab, App("diff", (Var("x"), Var("y"))), Mode.GE, {})

```

    [{'x': 0, 'y': 1}, {'x': 0, 'y': 2}, {'x': 0, 'y': 3}]

# Bits and Bobbles

All told, I find refinement a shockingly simple extension of the usual egraph concepts and implementation. But it has felt mysterious before so maybe that means I've just become incredibly wise?

I think really the thing that makes it shockingly simple is just not believing there is any incredibly clever or nuanced way of doing it. I think the only way to do it is basically the obvious way.

I think that maybe the generalization of all this is an egraph rewriting system that supports multiple relations and annotations of how they push through function symbols, akin to <https://rocq-prover.org/doc/V9.2.0/refman/addendum/generalized-rewriting.html>

I remember being at a table at PLDI 2022 and Zach trying to convince / ask John Regehr what he wanted for e-graph to be compelling to him. He said refinement and as a treatment of arbitrary bitwidth bitvectors. These two have stuck with me as things to look for and this is the source of the refinement e-graph line of questioning.

Other applications:

- Logic. `->` as a less than relation
- Relation algebra
- Algebra of Programming <https://www.philipzucker.com/a-short-skinny-on-relations-towards-the-algebra-of-programming/> bird and de Moor, Oliveira, Backhouse, Dijkstra <http://www.mathmeth.com/read.shtml>
- Subtyping
- Query containment
- First class lattice analyses

Extraction may want a frontier of <= eclasses from the union find if it wants to get the most refined term. That could be another function in the interface

I have debated rather than the mode + variance abstraction to allow specifying what expansion (EQ,GE,LE) you want in the language of the pattern. For example i could use `(foo ?a)`, `[foo ?a]`, `{foo ?a}` if I want to allow EQ, GE, LE respectively. This would allow fine grained ad hoc control of refinement e-matching in the pattern.

As Graham noted, the upper and lower sets of the Ids do fit operationally somewhat into the egg notion of Analyses. Generically, it makes perfect sense to have things keyed on `Id` that merge when `Id` merge. I am agnostic if that means such things must be Lattices (as many program analyses are), Semigroups (like eclass member counts) or something else. That the upper and lower sets themselves contain more Ids is fine but also defies a simple algebraic characterization of what is going on in my opinion.

There has been a similar debate if _equality_ is "just a lattice of partitions", trying to subsume the equality relation of the egraph into Lattices as the master concept. Didn't seem to really work but operationally it kind of makes sense that equalities is implemented as a "merge action" very much akin to a lattice join at least operationally. There is spooky action at a distance through the union find though. Mutable references often enable some kind of spooky tunnelling phenomenon that break simple mathematical models <https://counterexamples.org/polymorphic-references.html> <https://en.wikipedia.org/wiki/Value_restriction> (Oleg Kiselyov had some way of casting types through a ref cell tunnel too?)

| Current mode   |  Arg polarity  |    |
| =              |   _            | =  |
| <=             |   +            | <= |
| <=             |   =            | =  |
| <=             |   -            | >= |

The mode extraction kind of says what kind of pattern we are procssing   `p <= t`  `t <= p` or `t = p`.  `Variance` is a property of function symbols that says what we can infer about pushing `<=` through `f`. This is used in the upward direction for refinement closure,  but in the downward direction for breaking apart a pattern matching constraint/query into queries on the arguments  `{f(?a, ?b) R f(x,y)} ===> {?a R x, ?b R y}`. `R` may be flipped, kept the same, or forced to be equality because `f` isn't known to be sufficiently monotone. It is always sound to revert  an inequality query `?p <= t` to equality `?p = t`.

Extraction also comes in the same modes `t = ?extract`  `t <= ?extract` `t >= ?extract`. Extraction is kind of similar to pattern matching in some respects

 `[[x]] = fun b => {b}` is the lifted identity function. `ite` is pointwise lifted. `[[dontcare]] = fun _ => {True, False}` `[[true]] = fun _ => {True}` `[[false]] = fun _ => {False}`. Refinement is interpreted as subrelation.

I feel that for an abstract partial order relation, this is about as good as you're going to do. I don't think there is a some magic data structure that will make everything all better

But I do think there is the possibility to do better on two axes

- Partial Orders with extra axioms. Total, linear, Tree-like orders may have more available <https://microsoft.github.io/z3guide/docs/theories/Special%20Relations/>
- Proof relevancy. If you can say _the sense_ that `r : a <= b` then you can do better. As an example, if you know `a <= b` in the integers, a proof object might be an `n >= 0` such that `a + n == b`. This can be implemented as an offset union find, which is much more efficient. There are other orders where the proof object can help that generalize this. Tree-like orders in particular are interesting in that the tree-like ness of the order can comply nicely with the tree-like ness of the union find forest.
- Semantics. If we know we're talking about the integers with `<=`, yeah there might be a bunch of ways of going aobut it. It's total, yada yada, but we have a lot of games and data structures we can play on the integers. Side car linear programming solvers something something.

A prototype of a refinement egraph based on Max Willsey's microegg <https://github.com/mwillsey/microegg>. A WASM demo is here <https://www.philipzucker.com/refinement-microegg>

Refinement e-graphs give you an uninterpreted `<=` that is about as baked in as `=` is.

This is useful perhaps because as the story goes, many rewrites in compilers are not unoriented equalities, they are oriented refinements.

`<=` is baked in to be transitive, reflexive, and collapses cycles to `=`.

Previous discussions of mine on refinement e-graphs:

- <https://www.philipzucker.com/asymmetric_complete/> An Inequality Union Find Inspired by Atomic Asymmetric Completion
- <https://www.philipzucker.com/le_find/> Inequality Union Finds: Baby Steps to Refinement E-graphs

The union find tracks upper and lower `<=` sets in a manner similar to an analysis (they are keyed on eclass and merge on union). Tentatively, storing this maximally sparsely rather than fully materializing (DFSing it on demand) as one would in egglog is more performant in memory and time. [Egglog](https://github.com/egraphs-good/egglog) itself is highly engineered though, so I don't actually know how this shakes out.

A nice example is "don't care" in boolean circuits . Some inputs are not expected or allowed, so they optimizer is free to pick a behavior on those inputs that helps make a more optimal circuit.

In either case, I think baking in `<=` rather than having it as a mangled program or macro is conceptually cohesive and pleasant.

Nothing involving `<=` is quite as well behaved or as performant as `=`, but it is there as a light sprinkling on top. If _everything_ you do is refinement rather than equality, I am not sure the refinement egraph offers much over a hash cons with a stored inequality table.

E-matching, rebuilding, and extraction all have slight tweaks related to `<=`. Rebuilding performs refinement closure.

Function symbols can be given a variance signature, very similarly to variance of type parameters in subtyping. This is about whether they are monotone `a <= b -> f a <= f b`, anti-monotone `a <= b -> f a >= f b` or neither in particular arguments. This changes patterns and extraction "modes" appropriately as they go through the term.

Refinement rebuilding / closure is no where near as nice as equality (although it is still conceptually simple). It is not obvious that it will terminate if one allows new enode creation, so in that sense it is in the same naughty category as rewrite rules. There is a distinction to be made between materializing and non-materializing refinement closure (only note inequalities between pre-exising enodes).

You do sometimes want to enumerate your upper or lower set of ids for refinement closure, and for e-matching modulo refinement and extraction modulo refinement.

It is my belief that a completely generic uninterpreted refinement relation can never be as good as an equality relation and that there probably isn't an astonishingly good way of implementing such a thing. It will more or less correspond to depth first search enumerations +- some tweaks.

Nevertheless, I think it is both nontrivial, interesting, and possibly useful to bake in an inequality relation into the surface language and features.

The alternative is to macro encode an inequality into something like egglog. I kind of prefer direct operational interpretations than a macro expansion explanation.

In small micro benchmarks it does appear that maintaining the sparse representation of the inequality relation with on the fly closure is superior to materializing it ahead of time in memory and speed (memory often implies speed since cache whatevers are a dominant concern).

Based on the results in <https://www.sciencedirect.com/science/article/pii/S1571066104002968> it is my suspicion that ground refinement closure may be undecidable. In this case, full refinement closure should be treated at the same level of suspicion and incompleteness as rules are.

<https://www.philipzucker.com/asymmetric_complete/>

Hmm. Am i crazy? It would be nice is some enodes were subsumed by the inequality relation. But ematching can kind of traverse non materialized nodes? Is there some way we could subsume / del  / dematerialize enodes such that ematching could still find them?
Something that is pinned between f0 <= f1 <= f2 maybe we could del f1? Asymmetric rewriting still has some deletion character to it.
Maybe it oculd be the ematcher's job to materialize stuff a la Max's suggestion.

# 4/2026

It's kind of like knownbits. For BV1 it is all possible sets.

```python
from kdrag.all import *

none = smt.K(smt.BoolSort(), False)
true = smt.Store(none, True,True)
false = smt.Store(none, True, False)
any = smt.K(smt.BoolSort(), True)

def SetLift(f : FuncRef)
    ds = smt.domains(f)
    r = smt.range(f)
    def res(*args):
        x = smt.FreshConst("x", smt.BoolSort())
        ps = [smt.FreshConst("p", typ) for typ in ds]
        return smt.Lambda([x], smt.Exists(ps, x == args[0][p], x = f(p)))
    return res



def And(a, b):
    x = smt.FreshConst("x", smt.BoolSort())
    p,q = smt.Consts("p q", smt.BoolSort())
    return smt.Lambda([x], smt.Exists([p,q], a[p], b[q], x = smt.And(p,q)))

def Or(a, b): ...
def Implies()

obool = kd.inductive("inductive obool where | none : obool | lit : Bool -> obool | any : obool")

obool.lit(True)
x,y = smt.Consts("x y", obool)
kd.notation.and_.define([x,y], 
                        kd.cond(
                            (smt.And(x == obool.none, y == obool.none), obool.none),
                            ()
                        )
                        )

refines(a,b)


```

lit(True)

George example

simplify dontcare /\ x

0 /\ x = 0 is eq

Semantics is set of

For total orders there is are speical datastructure. What about one tjat effectively assigns "rationals"
Or really we have a space with gaps and we incrementally grow the space when it gets too full, or redistrbute if it gets too cluttered in just one section.

For tree orders, maybe we really could maintain a union find?

k-Width partial orders or approximation by a k-width order?

<https://microsoft.github.io/z3guide/docs/theories/Special%20Relations/>

Using partial order special relation to get refinement egraphs.
Need to manually order close though.

```python

```

<https://docs.google.com/document/d/15amCalh9CSOWbbZ3d_haNad0Pw_jJ7vYcjMLkp7r-AA/edit?tab=t.0>

polar types in dolan. Maybe something like this restriction enables ground asym completion to terminate? Separate refinement closure into its polar and non polar components.

lattice and ordered resolution
<https://cstheory.stackexchange.com/questions/12326/unification-and-gaussian-elimination> respond here once I get it

Unification and Knuth Bendix.
I consider them to be opposites even if they can be encoded to each other.
KB is forward reasoning
unification is backward reasoning from a query or goal

For speed reasons maybe you'd want to have 3-tuple 4-tuples etc available. Lempel ziv something something? <https://en.wikipedia.org/wiki/Lempel%E2%80%93Ziv%E2%80%93Welch>
word equqation solving also had compression as an idea in there...

string rewriting is a suffiicnet framework to simplify atomic equational proofs. Maybe overly powerful?

Why can't I binarize into a normal form
weight by original size. Tie break
abc = df
a b = e1
e1 c = e2

actual equations:
e2 = e4

overlaps
a b = e2
b c = e5

a + b = e_+1
a *b = e_*7
structured eids tagged by function symbol and identifier
Online extraction?
idenitfy a term with the eid at time of creation. You can on demand compare

"enodes" + "union find"
Nontrivial enode overlap is impossible. simplification is possible.
Weighted union find = weighted Atomic KBO

```
class UF():
    weight : list[int]
    parents : list[int]
    def union():
        x,y = find(x), find(y)
        if weight[x] <= weight[y]:
            parents[x] = y
        else:
            parents[x]
```

For AC enodes, we do need to perform overlap. Term ordering matters (?)
(X + Y + Z) :- (X + Y), (Y + Z).
Online extraction - we do not need to keep anything that

Teitze transformations <https://en.wikipedia.org/wiki/Tietze_transformations>
tsetsin
ANF
definitional exte4nsions
But would this be crazy for multiset, linear, grobner, etc?
ax + by = z1
x + by = z1
z1 = z2

ax + by = z1
where a b are coprime
ax + by = z1
a z1 = b z2

binary form of egraph. Partial application. App form
(f, x) = fx
(fx, y) = fxy
(fxy, z) = fxyz
LFHOL term orderings. Cody had some spiel

enodes need an overlap api. eids need online extraction / term orderings to figure out winners. Or just online extraction?
But why does ordering matter then if the term associated with eclass is fluid.
f(x,y,z) -> e1 can spontaneously become  unoriented in this perspective if x lowers a bunch
extraction repair f(x,y,z) <- e1

memo : enode -> eclass
parents : eclass -> eclass
enodes : eclass -> Vec<enode>  // vec?
weights : eclass -> Int

enodes kind of performs extraction
If there are two directions, that's an overlap / confluence problem. Need to remove stuff from union find?

Conservative extension makes sense either in compression or expansive form (decoding). efresh -> term decoding vs term -> egraph compressive

Knuth Bendix + definition extension / teitze, conservative extension

```
E, R, TermOrder
--------------define
E U {efresh = t}, R, TermOrder U {?}
```

Why is a careful term ordering seemingly necessary for stuff besides union finds and straight egraphs?

well ordering surgery. Ordinals (total well orders) have an otion of algebra. They have a uniquer global minimum.

AC egrapha = ground completion +
multiple ac symbols.
ACRPO - flatten + use multiset ? No but first we have to consider the exact structure we've been given
Rubio <https://courses.grainger.illinois.edu/cs576/sp2017/readings/18-mar-9/rubio-ac-rpo-long.pdf> a fully syntactic acrpo
<https://arxiv.org/pdf/1403.0406> ACKBO
<https://courses.grainger.illinois.edu/cs576/sp2017/readings/18-mar-9/narendran-rusinowitz-ground-AC-compl.pdf>
A \/ C, rpo
<https://courses.grainger.illinois.edu/cs576/sp2017/> meseguer readonig course. Pretty interesting stuff in here.
<https://courses.grainger.illinois.edu/CS476/fa2022/>
<https://courses.grainger.illinois.edu/CS476/fa2022/readings/meseguer-set-theory-algebra-computer-science.pdf> Set Theory and Algebra in Computer Science
A Gentle Introduction to Mathematical Modeling
order sorted algebras. hmm.
<https://dl.acm.org/doi/book/10.5555/547173> Algebraic Semantics of Imperative Programs
<https://courses.grainger.illinois.edu/cs476/sp2012/hw/lecture-notes-peter.pdf> Formal Modeling and
Analysis of Distributed
Systems in Maude

<https://www.lix.polytechnique.fr/~jouannaud/articles/acrvf.pdf>

<https://www.sciencedirect.com/science/article/pii/S0304397506002647> Abstract canonical presentations
proofs orderings. Good proofs.
<https://link.springer.com/chapter/10.1007/11780274_26> Completion Is an Instance of Abstract Canonical System Inference

<https://github.com/postechsv/maude-se>

```python
import maude
maude.init()
nat = maude.getModule('NAT')
t = nat.parseTerm('1 + 2')
t.reduce()
print(t)
```

    3

```python
t = nat.parseTerm('1 + 2')
t.symbol()
list(t.arguments())
#maude.Symbol()
nat.parseTerm("X + Y")
```

    [31mWarning: [0m<standard input>, line 0: bad token [35mX[0m.
    [31mWarning: [0m<standard input>, line 0: no parse for term.

```python
maude.getModules()
```

    (fmod BOOL,
     fmod TRUTH-VALUE,
     fmod BOOL-OPS,
     fmod TRUTH,
     fmod EXT-BOOL,
     fmod INITIAL-EQUALITY-PREDICATE,
     fmod NAT,
     fmod INT,
     fmod RAT,
     fmod FLOAT,
     fmod STRING,
     fmod CONVERSION,
     fmod RANDOM,
     fmod BOUND,
     fmod QID,
     fth TRIV,
     fth STRICT-WEAK-ORDER,
     fth STRICT-TOTAL-ORDER,
     fth TOTAL-PREORDER,
     fth TOTAL-ORDER,
     fth DEFAULT,
     fmod LIST,
     fmod WEAKLY-SORTABLE-LIST,
     fmod SORTABLE-LIST,
     fmod WEAKLY-SORTABLE-LIST',
     fmod SORTABLE-LIST',
     fmod SET,
     fmod LIST-AND-SET,
     fmod SORTABLE-LIST-AND-SET,
     fmod SORTABLE-LIST-AND-SET',
     fmod LIST*,
     fmod SET*,
     fmod MAP,
     fmod ARRAY,
     fmod STRING-OPS,
     fmod NAT-LIST,
     fmod QID-LIST,
     fmod QID-SET,
     fmod META-TERM,
     fmod META-CONDITION,
     fmod META-STRATEGY,
     fmod META-MODULE,
     fmod META-VIEW,
     fmod META-LEVEL,
     fmod LEXICAL,
     mod COUNTER,
     mod LOOP-MODE,
     mod CONFIGURATION)

```python
import maude
maude.init()
#nat = maude.getModule('NAT')
#list(nat.getSymbols())
#maude.input("load Nat .")
#maude.input("vars X Y : Nat .")
mod = maude.getCurrentModule()
list(mod.getSymbols())
list(mod.getSorts())

maude.input("""
fmod SIMPLE-NAT is 
       sort Nat . 
       op zero : -> Nat . 
       op s_ : Nat -> Nat . 
       op _+_ : Nat Nat -> Nat . 
       vars N M : Nat . 
       eq zero + N = N . 
       eq s N + M = s (N + M) . 
      endfm
""")
sn = maude.getModule("SIMPLE-NAT")
sn.parseTerm("s s N")

from dataclasses import dataclass, field
type Sort = str
@dataclass
class ModuleBuilder():
    name : str
    sorts : set[Sort] = field(default_factory=set)
    vars : dict[str, Sort] = field(default_factory=dict)
    ops : dict[str, tuple[list[Sort], Sort]] = field(default_factory=dict)
    extras : list[str] = field(default_factory=list)
    def build(self) -> str:
        maude.input(str(self))
        return maude.getModule(self.name)
    def add_sort(self, sort: smt.SortRef):
        self.sorts.add(sort.name())
    def add_decl(self, decl: smt.FuncDeclRef):



    def __str__(self):
        lines = [f"fmod {self.name} is"]
        for s in self.sorts:
            lines.append(f"  sort {s} .")
        for v, s in self.vars.items():
            lines.append(f"  var {v} : {s} .")
        for op, (arg_sorts, ret_sort) in self.ops.items():
            arg_str = ' '.join(arg_sorts)
            lines.append(f"  op {op} : {arg_str} -> {ret_sort} .")
        lines.extend(self.extras)
        lines.append("endfm")
        return '\n'.join(lines)


ModuleBuilder()
```

    [32mAdvisory: [0mredefining module [35mSIMPLE-NAT[0m.

```python
maude.__file__
```

    '/home/philip/philzook58.github.io/.venv/lib/python3.12/site-packages/maude/__init__.py'

```python
nat
```

    NAT

```python
maude.getModule("SMT")
```

```python
class StringKB():
    memo : dict[object,int]
    compress : dict[[tuple[int,int], int]]
    # repeat : dict[tuple[EId, int], EId]
    uf : list[int]
    def makeset(self):
        self.uf.append(len(self.uf))
        return len(self.uf) - 1
    def memo_obj(self, x):
        if x in self.memo:
            return self.memo[x]
        else:
            i = self.makeset()
            self.memo[x] = i
            return i
    def add_str(self, xs):
        xs = map(self.memo_obj, xs)
        for i in range(len(xs) - 1):
            a,b = xs[i], xs[i+1]
            if (a,b) in self.compress:
                c = self.compress[(a,b)]
            else:
                c = self.makeset()
                self.compress[(a,b)] = c
    def union(self, a, b):
        ra = self.find(a)
        rb = self.find(b)
        if ra != rb:
            self.uf[ra] = rb
    def rebuild(self):
        for (a,b), c in self.compress.items(): # overlap
            for (d,e), f in self.compress.items():
                if self.find(b) == self.find(d):
                    ce, af = self.pair(c,e), self.pair(a,f)
                    self.union(ce, af)
        for (a,b), c in self.compress.items(): # congruence
            ra, rb, rc = self.find(a), self.find(b), self.find(c)
            self.union(self.pair(ra,rb), rc)
        

            
    

```

```python
def reclen(t1):
    if isinstance(t1, tuple):
        return 1 + sum(map(reclen, t1))
    else:
        return 1

reclen((((1,2),3)))
```

    5

```python
def lt_kbo(t1, t2):
    # ground kbo is size + tie breaking
    if t1 == t2:
        return False
    elif isinstance(t1, tuple) and isinstance(t2, tuple):
        l1, l2 = reclen(t1), reclen(t2)
        if l1 < l2:
            return True
        elif l1 > l2:
            return False
        else:
            for a,b in zip(t1,t2):
                if a == b:
                    continue
                else:
                    return lt_kbo(a,b)
    elif not isinstance(t1, tuple) and not isinstance(t2, tuple):
        return t1 < t2
    elif not isinstance(t1, tuple) and isinstance(t2, tuple):
        return True
    else:
        return False

lt_kbo((1,2),(1,3))
lt_kbo((1,2),(1,2,3))
lt_kbo((1,2,3),(1,2))
```

    False

a lambda egraph. (but only alpha)
Why not?

did I ever do a KB egraph?

```python
def replace(t, lhs, rhs):
    if t == lhs:
        return rhs
    elif isinstance(t, tuple):
        return tuple(lambda x: replace(x, lhs, rhs) for x in t)
    else:
        return t



```

```python
class EGraph():
    rules : dict

    def union(self, t1, t2):
        t1,t2 = self.canon(t1), self.canon(t2)
    def find(self, t): ...
    def rebuild(self, t):
        foself.rules.keys():


```

```python



def lt_kbo(t1, t2):
    # ground kbo is size + tie breaking
    if reclen(t1) < reclen(t2):
        return True
    else:
        
def rw(t, lhs, rhs):
    if t == lhs:
        return rhs
    elif isinstance(t, tuple):
        return tuple(map(rw(lhs,rhs), t))
    else:
        return t


class AsymComplete():

```
