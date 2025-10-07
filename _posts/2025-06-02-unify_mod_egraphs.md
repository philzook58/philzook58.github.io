---
title: Unification Modulo E-Graphs
date: 2025-06-02
---

I think there are reasonable ways to add an e-graph to [unification](https://en.wikipedia.org/wiki/Unification_(computer_science)) algorithms.

This would correspond to e-unification <https://www.cs.bu.edu/fac/snyder/publications/UnifChapter.pdf> with the theory E being the ground equalities the e-graph represents. That's a reasonably well formed notion. Carrying a changing e-graph in the state would support logic programming and theorem provers with a slightly richer notion of `=`. One could call it maybe CLP(EGraph).

I don't have how to do this exactly nailed down, but the way we make progress is by saying stuff. So here we go.

## Basic Unification

First let's look at an implementation of basic syntactic unification

Unification processes a set of goals equations. It chews on them, adding them to a substitution when it can.

The loop based version of it corresponds fairly directly to the declarative rule system. I use eager substitution to retain clarity, although it's probably less efficient.

![](https://www.philipzucker.com/assets/traat/unify_rules.png)

For a deeper dive, see this blog post <https://www.philipzucker.com/unify/>

```python
from kdrag.all import *

def unify(vs: list[smt.ExprRef], p1: smt.ExprRef, p2: smt.ExprRef) -> Optional[dict[smt.ExprRef, smt.ExprRef]]:
    subst = {}
    todo = [(p1, p2)]

    def is_var(x):
        return any(x.eq(v) for v in vs)

    while todo:
        p1, p2 = todo.pop()  # we could pop _any_ of the todos, not just the top.
        if p1.eq(p2):  # delete
            continue
        elif is_var(p1):  # elim
            if occurs(p1, p2):
                return None
            todo = [
                (smt.substitute(t1, (p1, p2)), smt.substitute(t2, (p1, p2)))
                for (t1, t2) in todo
            ]
            subst = {k: smt.substitute(v, (p1, p2)) for k, v in subst.items()}
            subst[p1] = p2
        elif is_var(p2):  # orient
            todo.append((p2, p1))
        elif smt.is_app(p1):  # decompose
            if not smt.is_app(p2) or p1.decl() != p2.decl():
                return None
            todo.extend(zip(p1.children(), p2.children()))
        else:
            raise Exception("unexpected case", p1, p2)
    return subst
```

## Naive Unification Modulo E-Graphs

A naive method is to replace the failure point of disequal function symbols `f != g` with instead adding it to a constraints list. Then at the end, this constraints list may be solved by e-matching against an egraph `E`. After all, just because `foo(X)` can't be syntactically unified with `bar(z)` doesn't mean there aren't groundings that make it work in the egraph.

I'm using the egraph implementation based around z3 I described here <https://www.philipzucker.com/brute_eggmt/> . It's been very nice having a simple egraph I have in a library to play with.

```python
from kdrag.all import *
from kdrag.solvers.egraph import EGraph
from typing import Optional

def eunify_naive(vs: list[smt.ExprRef], p1: smt.ExprRef, p2: smt.ExprRef, E : EGraph) -> list[dict[smt.ExprRef, smt.ExprRef]]:
    subst = {}
    todo = [(p1, p2)]
    constrs = []

    def is_var(x):
        return any(x.eq(v) for v in vs)

    while todo:
        p1, p2 = todo.pop()
        if p1.eq(p2):  # delete
            continue
        elif is_var(p1):  # elim
            if kd.utils.occurs(p1, p2):
                constrs.append((p1, p2))
            else:
                todo = [
                    (smt.substitute(t1, (p1, p2)), smt.substitute(t2, (p1, p2)))
                    for (t1, t2) in todo
                ]
                subst = {k: smt.substitute(v, (p1, p2)) for k, v in subst.items()}
                subst[p1] = p2
        elif is_var(p2):  # orient
            todo.append((p2, p1))
        elif smt.is_app(p1):  # decompose
            if not smt.is_app(p2) or p1.decl() != p2.decl():
                constrs.append((p1, p2))
            todo.extend(zip(p1.children(), p2.children()))
        else:
            raise Exception("unexpected case", p1, p2)
    constrs = [
                (smt.substitute(t1, *subst.items()), smt.substitute(t2, *subst.items()))
                    for (t1, t2) in constrs
                ]
    print("constrs", constrs)
    if all(E.is_eq(c1, c2) for c1, c2 in constrs):
        return [subst]
    else:
        rem_vs = list(set(vs) - set(subst.keys()))
        if len(rem_vs) == 0:
            return []
        substs = []
        # Bottom up ematching to solve the constraints
        for ts in E.iter(rem_vs):
            if all(E.is_eq(smt.substitute(c1,*zip(rem_vs, ts)), smt.substitute(c1,zip(rem_vs, ts))) for c1,c2 in constrs):
                substs.append({**subst, **dict(zip(rem_vs, ts))})
        return substs
```

This example succeeds in a normal way using syntactic unification

```python
E = EGraph()
x,y,z = smt.Ints("x y z")
a,b,c = smt.Ints("a b c")

eunify_naive([x], x ** a, a ** x, E)
```

    constrs []





    [{x: a}]

This example fails to unify syntactically

```python
E = EGraph()
eunify_naive([x], x ** b, a ** x, E)
```

    constrs [(b, a)]





    []

But under the assumption `a = b` going into the egraph now it can succeed.

```python
E = EGraph()
E.union(a, b)
eunify_naive([x], x ** a, b ** x, E)
```

    constrs [(a, b)]





    [{x: a}]

## Better (or just different?)

This naive approach is incomplete in at least this sense: We cannot eagerly take the decompose moves. The egraph offers a new rule
`EMatch : {t1 = t2} uplus S  ===>  {sigma uplus sigma(S) | sigma in E.ematch(vs,t1,t2) }`  where the substitutions come from e-matching against the e-graph.

We have a nondeterminism because this e-matching rule is nondeterminstic and because we don't know whether to apply decompose and this rule. Huge bummer.

As an example of the failure consider the goal equation `foo(X,a) =? foo(b,c)` and an egraph containing the equality `foo(b, a) = foo(b,c)`. We take a decompose move  to `{X =? b, a =? c}` and have solved `X` now. But we have unification failure on `a =? c` so we switch to e-matching. But we don't have `a = c` in the egraph either, so the above naive procedure fails. Nevertheless, the substitution `X = b` does actually solve the goal equation modulo the egraph equations.

```python
foo = smt.Function("foo", smt.IntSort(), smt.IntSort(), smt.IntSort())
E = EGraph()
E.union(foo(b,a), foo(b,c))
eunify_naive([x], foo(x, a), foo(b, c), E)
```

    constrs [(a, c)]





    []

What you have to do is actually search instead of eagerly taking the decompose step. At every possible decompose step, you should also switch into e-matching mode at that point too. I _think_ this methodology would get you a complete set of solutions for unification modulo e-graphs.

What I think makes the most sense is a deeply integrated unifier and top down ematcher. That isn't really what I have here though. I have avoided writing top down ematchers recently. I should try though.

Instead, here is the brute force form of just taking every possible ematch vs decompose move.

```python
def eunify2(vs: list[smt.ExprRef], p1: smt.ExprRef, p2: smt.ExprRef, E : EGraph) -> list[dict[smt.ExprRef, smt.ExprRef]]:
    subst0 = {}
    todo0 = [(p1, p2)]
    constrs0 = []
    branches = [(todo0, subst0, constrs0)]
    res = []

    def is_var(x):
        return any(x.eq(v) for v in vs)

    while branches:
        todo, subst, constrs = branches.pop()
        while todo:
            p1, p2 = todo.pop()
            if p1.eq(p2):  # delete
                continue
            elif is_var(p1):  # elim
                #if kd.utils.occurs(p1, p2):
                #    return None
                todo = [
                    (smt.substitute(t1, (p1, p2)), smt.substitute(t2, (p1, p2)))
                    for (t1, t2) in todo
                ]
                subst = {k: smt.substitute(v, (p1, p2)) for k, v in subst.items()}
                subst[p1] = p2
            elif is_var(p2):  # orient
                todo.append((p2, p1))
            elif smt.is_app(p1):  # decompose
                branches.append((todo.copy(), subst.copy(), constrs + [(p1,p2)]))
                if smt.is_app(p2) and p1.decl() == p2.decl():
                    todo.extend(zip(p1.children(), p2.children()))
            else:
                raise Exception("unexpected case", p1, p2)
        constrs = [
                    (smt.substitute(t1, *subst.items()), smt.substitute(t2, *subst.items()))
                        for (t1, t2) in constrs
                    ]
        if all(E.is_eq(c1, c2) for c1, c2 in constrs):
            res.append(subst)
        else:
            rem_vs = list(set(vs) - set(subst.keys()))
            if len(rem_vs) == 0:
                continue
            for ts in E.iter(rem_vs):
                if all(E.is_eq(smt.substitute(c1,*zip(rem_vs, ts)), smt.substitute(c1,zip(rem_vs, ts))) for c1,c2 in constrs):
                    res.append({**subst, **dict(zip(rem_vs, ts))})
    return res

foo = smt.Function("foo", smt.IntSort(), smt.IntSort(), smt.IntSort())
E = EGraph()
E.union(foo(b,a), foo(b,c))
eunify2([x], foo(x, a), foo(b, c), E)
```

    [{x: b}]

# Bottom Up E-Unification

I have been pushing bottom up e-matching <https://arxiv.org/abs/2504.14340> . It also seems to work for unification. You can guess unification solutions because they are seeded out of the unification problem terms themselves.

I can just use my dumb dumb bottom up ematching to perform E-unification by adding the pattern terms as possible seeds in the egraph.

I think this kind of works. I'm not so sure about completeness.

It also does get you theory understanding from z3 which is also pretty awesome. And damn tootin is this some short code.

```python
import itertools
from kdrag.solvers.egraph import EGraph
from kdrag.all import *

def eunify(vs, t1, t2, E=None):
    if E is None:
        E = EGraph()
    else:
        E = E.copy()
    E.add_term(t1)
    E.add_term(t2)
    E.rebuild()
    res = [] 
    for ts in E.iter(vs):
            lhs = smt.substitute(t1, *zip(vs, ts))
            rhs = smt.substitute(t2, *zip(vs, ts))
            with E.solver:
                E.solver.add([v == t for v,t in zip(vs, ts)])
                if E.solver.check() == smt.unsat: # substitution is semantically viable
                    continue
                E.solver.add(lhs != rhs) # substitution does force lhs == rhs
                if E.solver.check() == smt.unsat:
                    res.append(dict(zip(vs, ts)))
    return res

x,y,z = smt.Ints("x y z")
a,b,c = smt.Ints("a b c")
foo = smt.Function("foo", smt.IntSort(), smt.IntSort(), smt.IntSort())
E = EGraph()
E.union(foo(b,a), foo(b,c))
eunify([x], foo(x, a), foo(b, c), E)
```

    [{x: b}]

# Bits and Bobbles

Pavel has been making the connection that pattern matching modulo theories is related to quantifier elimination. Syntactic unification is kind of quantifier elimination for the theory of algebraic datatypes (which have the injectivity to support "decompose" and have wellfoundedness enforced by the occurs check).

- <https://pavpanchekha.com/blog/lin-graphs.html>
- <https://pavpanchekha.com/blog/egraph-t.html>
- <https://pavpanchekha.com/blog/p-graphs.html>

 I have actually felt this while building pattern matchers in knuckledragger. Pattern variables are implicitly existentially quantified. If smt had a choice quantifier, that'd be great.

Functional Logic programming would be the better target of integration I'd think. Are egraphs useful as part of tabling in FLP?

One place where equalities have shown up in LP is for trait resolution in Rust with associated types. <https://doc.rust-lang.org/rust-by-example/generics/assoc_items/types.html> These become introduced equalities during the prolog like trait resolution search <https://rust-lang.github.io/chalk/book/what_is_chalk.html>
 <https://github.com/rust-lang/chalk> . Maybe unification modulo egraphs could help here. Not so sure.

I've seen some discussion of bottom up unification for higher order unification in Gilles dowek's chapter in the handbook of automated reasoning. It is introduced as merely a conceptual device though. Maybe one should implement it? But also I should implement actual Huet unification.

The z3 ematching paper <https://leodemoura.github.io/files/ematching.pdf> is kind of a Warren abstract machine. <https://direct.mit.edu/books/monograph/4253/Warren-s-Abstract-MachineA-Tutorial-Reconstruction>

CHR egraph <https://www.philipzucker.com/egraph-chr/> might be another way to embed egraph in prolog

Unification is double sided pattern matching. It's logic talk for equation solving. You are presented a set of goals equations with variables and you want to produce a substitution (at least in the narrow sense of equation solving) to those variables to make the equations hold.

Unification powers logic programming like prolog and more so than the other ingredient of backtracking/search, powers the bidirectional flavor of the subject.

Unification usually starts from a standpoint of syntactic unification where every function symbol is considered to be injective akin to an algebraic datatype. This makes life easier.

There is also E-unification, unification modulo some background theory E, like baked in linearity, booleans, associativity etc.

Unification modulo E-graphs is E-unification modulo the theory E of ground equations the egraph represents.

- <https://en.wikipedia.org/wiki/Unification_(computer_science)>
- <https://www.philipzucker.com/unify/>

I would think that e-graphs might also be used as a form of tabling for functional logic programming.

One version of this might be to try regular unification and if at any point that fails at pattern `p1 =? p2`, try to solve the unsolvable equation by double sided e-matching in an E-graph (ie is the a grounding of the variables in p1 and p2 such that the egraph asserts them equal).

This isn't particularly complete but has the advantage of less search compared to other methods.

Ok, I could switch over to ematching in a simple way becasue ematching is multivalued.

It is nice to make your unify just punt some stuff into a constraints list.

Ultimately, the substitutions of unification are seeded out of the original terms.
A bottom up form of unification if to guess every possible substitution out of some over approximation of the possible substitutions.

This is crazily inefficient from a syntactic unification perspective, but the more you add on theories, the more compelling it becomes.

The EGraph itself can become a unifier by adding the patterns to the egraph and performing regular bottom up ematching.

I think that non well-founded substitutions

To what degree is an non well-founded substitution better than the incoming goals? It represents a solution as a kind of rational tree.

```python
def unify(vs: list[smt.ExprRef], p1: smt.ExprRef, p2: smt.ExprRef) -> Optional[dict[smt.ExprRef, smt.ExprRef]]:
    subst = {}
    todo = [(p1, p2)]
    constrs = []

    def is_var(x):
        return any(x.eq(v) for v in vs)

    while todo:
        p1, p2 = todo.pop()  # we could pop _any_ of the todos, not just the top.
        if p1.eq(p2):  # delete
            continue
        elif is_var(p1):  # elim
            if occurs(p1, p2):
                return None
            todo = [
                (smt.substitute(t1, (p1, p2)), smt.substitute(t2, (p1, p2)))
                for (t1, t2) in todo
            ]
            subst = {k: smt.substitute(v, (p1, p2)) for k, v in subst.items()}
            subst[p1] = p2
        elif is_var(p2):  # orient
            todo.append((p2, p1))
        elif smt.is_app(p1):  # decompose
            if not smt.is_app(p2) or p1.decl() != p2.decl():
                constrs.append((p1, p2))
            todo.extend(zip(p1.children(), p2.children()))
        else:
            raise Exception("unexpected case", p1, p2)
    return subst, constrs
```

```python
def weak_eunify(
    vs: list[smt.ExprRef], p1: smt.ExprRef, p2: smt.ExprRef, E : EGraph
) -> Optional[dict[smt.ExprRef, smt.ExprRef]]:
    """Unification"""
    def is_var(x):
            return any(x.eq(v) for v in vs)
    branches = [({}, [(p1,p2)])]
    
    while branches:
        subst, todo = branches.pop()
        while todo:
            p1, p2 = todo.pop()  # we could pop _any_ of the todos, not just the top.
            if p1.eq(p2):  # delete
                continue
            elif is_var(p1):  # elim
                if occurs(p1, p2):
                    return None
                todo = [
                    (smt.substitute(t1, (p1, p2)), smt.substitute(t2, (p1, p2)))
                    for (t1, t2) in todo
                ]
                subst = {k: smt.substitute(v, (p1, p2)) for k, v in subst.items()}
                subst[p1] = p2
            elif is_var(p2):  # orient
                todo.append((p2, p1))
            elif smt.is_app(p1):  # decompose
                #if not smt.is_app(p2) or p1.decl() != p2.decl():
                # find vs in p1, p2
                for match_ in E.ematch(p1,p2):
                    tcopy = [
                        (smt.substitute(t1, match_), smt.substitute(t2, match_))
                        for (t1, t2) in todo.copy()
                    ]
                    scopy = subst.copy()
                    branches.append((scopy, tcopy))
                todo.extend(zip(p1.children(), p2.children()))
            else:
                raise Exception("unexpected case", p1, p2)
```

```python
def weak_eunify(vs,t1,t2,E):
    todo = [(t1,t2)]
    subst = {}
    while todo:
        t1, t2 = todo.pop()
        if t1.eq(t2):
            continue
        if isinstance(t1, str) and isinstance(t2, str):
            if t1 in vs or t2 in vs:
                E.append((t1, t2))
            else:
                return False
        elif isinstance(t1, list) and isinstance(t2, list):
            if len(t1) != len(t2):
                return False
            todo.extend(zip(t1, t2))
        else:
            return False

def better
def bottom_up_eunify()

```

full lambda unification
context unification
secord order unification
linear lambda unification

<https://stackoverflow.com/questions/1936432/higher-order-unification>

unif conference <https://www.irif.fr/~treinen/unif/>

# unification modulo egraphs

We can recurse down and choose to match subterms by either ematching or syntactic unification

Or we can go bottom up

Why?
E-KB is interesting.
Side car egraph in a prolog might be interesting.

You might think you can eagerly take

f(t) = f(s) ---> t = s
But you can't

consider an egraph f(a) = f(b)

and now we want to solve f(a) = f(b). We process it via the unification head rule to

<https://www.philipzucker.com/unify/>
![](https://www.philipzucker.com/assets/traat/unify_rules.png)

```
{t = s, S}  --->  sigma S ematch
```

We can't just eagerly take head peeling moves. The egraph may have f(x) = f(y) but not x = y. In which case peeling off f is a bad move.

We could pick different worlds at the outset. Is x a var or grounded?

```python
from kdrag.solvers import VampireSolver
import z3
T = z3.DeclareSort("T")
x,y,z = z3.Consts("x y z", T)
s = VampireSolver()
s.add(x != y)
s.check()





```

    (set-logic ALL)
    
    (declare-sort T 0)
    
    ;;declarations
    
    (declare-fun y_98 () T)
    
    (declare-fun x_97 () T)
    
    ;;axioms
    
    (assert (distinct x_97 y_98))
    
    (check-sat)
    
    b'WARNING Broken Constraint: if inner_rewriting(on) has been set then saturation_algorithm(fmb) is equal to lrs or saturation_algorithm(fmb) is equal to otter or saturation_algorithm(fmb) is equal to discount\nWARNING Broken Constraint: if inline_let(on) has been set then newcnf(off) is equal to on\nWARNING Broken Constraint: if inline_let(on) has been set then newcnf(off) is equal to on\nWARNING Broken Constraint: if inline_let(on) has been set then newcnf(off) is equal to on\nWARNING Broken Constraint: if inline_let(on) has been set then newcnf(off) is equal to on\nWARNING Broken Constraint: if inline_let(on) has been set then newcnf(off) is equal to on\nWARNING Broken Constraint: if symbol_precedence(reverse_arity) has been set then saturation_algorithm(fmb) is equal to lrs or saturation_algorithm(fmb) is equal to otter or saturation_algorithm(fmb) is equal to discount\nWARNING Broken Constraint: if sos(all) has been set then saturation_algorithm(fmb) is equal to lrs or saturation_algorithm(fmb) is equal to otter or saturation_algorithm(fmb) is equal to discount\nWARNING Broken Constraint: if literal_maximality_aftercheck(on) has been set then saturation_algorithm(fmb) is equal to lrs or saturation_algorithm(fmb) is equal to otter or saturation_algorithm(fmb) is equal to discount\nWARNING Broken Constraint: if lrs_weight_limit_only(on) has been set then saturation_algorithm(discount) is equal to lrs\nWARNING Broken Constraint: if literal_comparison_mode(predicate) has been set then saturation_algorithm(fmb) is equal to lrs or saturation_algorithm(fmb) is equal to otter or saturation_algorithm(fmb) is equal to discount\nWARNING Broken Constraint: if nongoal_weight_coefficient(1.7) has been set then saturation_algorithm(fmb) is equal to lrs or saturation_algorithm(fmb) is equal to otter or saturation_algorithm(fmb) is equal to discount\nWARNING Broken Constraint: if avatar(off) has been set then saturation_algorithm(fmb) is equal to lrs or saturation_algorithm(fmb) is equal to otter or saturation_algorithm(fmb) is equal to discount\nWARNING Broken Constraint: if inline_let(on) has been set then newcnf(off) is equal to on\nWARNING Broken Constraint: if lrs_weight_limit_only(on) has been set then saturation_algorithm(discount) is equal to lrs\nWARNING Broken Constraint: if inline_let(on) has been set then newcnf(off) is equal to on\nWARNING Broken Constraint: if inline_let(on) has been set then newcnf(off) is equal to on\nWARNING Broken Constraint: if inline_let(on) has been set then newcnf(off) is equal to on\nWARNING Broken Constraint: if inline_let(on) has been set then newcnf(off) is equal to on\nWARNING Broken Constraint: if inline_let(on) has been set then newcnf(off) is equal to on\nsat\n'
    b''

<b>sat</b>

```python
from kdrag.all import *
from kdrag.solvers.egraph import EGraph

def eunify(vs, t1, t2):
    todo = [(t1,t2)]
    while todo:
        t1, t2 = todo.pop()
        if t1.eq(t2):
            continue

# a different approach. Variables are preselected as to be ematched vs unified.
def eunify(avs, evs, t1, t2, E):
    def is_ground(t):
        return kd.utils.free_in(avs, t)
    if is_ground(t1):
        if is_ground(t2):
            if E.find(t1) != E.find(t2):
                return
        else:
            ematch(
    




```

    set()

Add top down capabilities.
eid + decl -> children
or decl -> (i,j,k) children and parent.

This would be good for an apples to apples comparison of the technqiues of top down vs bottom up.

Bottom up unification.
Can I bound all possible substitutions a priori?
Pick ordering
v1 = all subterms
subst back in

I think maybe v goes to all possible subterms?
Some well founded some not. But we don't want only well founded. Occurs check is for datatypes

Apply a substitution to the egraph that holds unification vars...
Maybe. It's a violent thing to do.

Hmm. Should I be checking that the unsats aren't because of impossibilities? Rather than the matching condition?

Wait. This isn't just unification modulo egraphs. It's unification modulo all the theories of z3. Just not a most general unifier.

Hmm. The theory of uninterpreted functions makes nearly everything a _possible_ solution? Except patent impossibilities.
Oh. Oh dear. Maybe that is a problem.
No. I'm insane.

```python
import itertools
from kdrag.solvers.egraph import EGraph
from kdrag.all import *

def eunify(vs, t1, t2, E=None):
    if E is None:
        E = EGraph()
    else:
        E = E.copy()
    E.add_term(t1)
    E.add_term(t2)
    E.rebuild()
    res = [] 
    for eids in itertools.product(*[E.roots[v.sort()] for v in vs]):
            ts = [E.terms[eid] for eid in eids]
            lhs = smt.substitute(t1, *zip(vs, ts))
            rhs = smt.substitute(t2, *zip(vs, ts))
            #if E.is_eq(lhs, rhs):
            with E.solver:
                E.solver.add([v == t for v,t in zip(vs, ts)])
                if E.solver.check() == smt.unsat: # substitution is semantically viable
                    continue
                E.solver.add(lhs != rhs) # substitution does force lhs == rhs
                if E.solver.check() == smt.unsat:
                    res.append((dict(zip(vs, ts)), lhs, rhs))
    return res

x,y,z = smt.Reals("x y z")
eunify([x,y], x + y, x + z)
```

    [({x: x, y: z}, x + z, x + z),
     ({x: y, y: z}, y + z, y + z),
     ({x: x + y, y: z}, x + y + z, x + y + z),
     ({x: x + z, y: z}, x + z + z, x + z + z),
     ({x: z, y: x}, z + x, z + z),
     ({x: z, y: z}, z + z, z + z)]

```python
def subsume(subst1, subst2, E): # subst1 implies subst2
    with E.solver:
        E.solver.add([v == t for v,t in subst1.items()])
        if all(E.is_eq(t1,t2) for t1, t2 in subst2.items()):
            return True
        else: 
            return False
        
def prune(substs, E=None):
    if E is None:
        E = EGraph()
    res = []
    for (subst, lhs, rhs) in substs:
        if any(subsume(s[0], subst, E) and subsume(subst, s[0], E) for s in res): # equivalent substitutions
            continue
        else:
            res.append((subst,lhs,rhs))
    return res
prune(eunify([x,y], x + y, x + z))
```

    [({x: x, y: z}, x + z, x + z),
     ({x: y, y: z}, y + z, y + z),
     ({x: x + y, y: z}, x + y + z, x + y + z)]

```python
foo = smt.Function("foo", smt.RealSort(), smt.RealSort(), smt.RealSort())
eunify([x,y], foo(x, y), foo(x, z))
```

    [({x: x, y: z}, foo(x, z), foo(x, z)),
     ({x: y, y: z}, foo(y, z), foo(y, z)),
     ({x: foo(x, z), y: z}, foo(foo(x, z), z), foo(foo(x, z), z)),
     ({x: z, y: x}, foo(z, x), foo(z, z)),
     ({x: z, y: z}, foo(z, z), foo(z, z)),
     ({x: foo(x, y), y: z}, foo(foo(x, y), z), foo(foo(x, y), z))]

```python
import kdrag.theories.nat as nat

n,m,k = smt.Consts("n m k", nat.Nat)
E = EGraph()
#E.union(nat.Z + nat.Z, nat.Z)
#E.union(nat.S(nat.Z) + nat.Z, nat.S(nat.Z))
#E.union(nat.Z + nat.S(nat.Z), nat.S(nat.Z))
#E.solver.add(nat.add.defn.thm)
eunify([n,m, k], nat.S(m) + n, k, E)




```

    ([({n: k, m: k, k: add(S(m), n)}, add(S(k), k), add(S(m), n)),
      ({n: k, m: m, k: add(S(m), n)}, add(S(m), k), add(S(m), n)),
      ({n: k, m: n, k: add(S(m), n)}, add(S(n), k), add(S(m), n)),
      ({n: k, m: add(S(m), n), k: m}, add(S(add(S(m), n)), k), m),
      ({n: k, m: add(S(m), n), k: add(S(m), n)},
       add(S(add(S(m), n)), k),
       add(S(m), n)),
      ({n: m, m: k, k: add(S(m), n)}, add(S(k), m), add(S(m), n)),
      ({n: m, m: m, k: add(S(m), n)}, add(S(m), m), add(S(m), n)),
      ({n: m, m: n, k: add(S(m), n)}, add(S(n), m), add(S(m), n)),
      ({n: m, m: add(S(m), n), k: m}, add(S(add(S(m), n)), m), m),
      ({n: m, m: add(S(m), n), k: n}, add(S(add(S(m), n)), m), n),
      ({n: m, m: add(S(m), n), k: add(S(m), n)},
       add(S(add(S(m), n)), m),
       add(S(m), n)),
      ({n: n, m: k, k: add(S(m), n)}, add(S(k), n), add(S(m), n)),
      ({n: n, m: m, k: add(S(m), n)}, add(S(m), n), add(S(m), n)),
      ({n: n, m: n, k: add(S(m), n)}, add(S(n), n), add(S(m), n)),
      ({n: n, m: add(S(m), n), k: m}, add(S(add(S(m), n)), n), m),
      ({n: n, m: add(S(m), n), k: add(S(m), n)},
       add(S(add(S(m), n)), n),
       add(S(m), n)),
      ({n: add(S(m), n), m: k, k: n}, add(S(k), add(S(m), n)), n),
      ({n: add(S(m), n), m: k, k: add(S(m), n)},
       add(S(k), add(S(m), n)),
       add(S(m), n)),
      ({n: add(S(m), n), m: m, k: n}, add(S(m), add(S(m), n)), n),
      ({n: add(S(m), n), m: m, k: add(S(m), n)},
       add(S(m), add(S(m), n)),
       add(S(m), n)),
      ({n: add(S(m), n), m: n, k: m}, add(S(n), add(S(m), n)), m),
      ({n: add(S(m), n), m: n, k: n}, add(S(n), add(S(m), n)), n),
      ({n: add(S(m), n), m: n, k: add(S(m), n)},
       add(S(n), add(S(m), n)),
       add(S(m), n)),
      ({n: add(S(m), n), m: add(S(m), n), k: m},
       add(S(add(S(m), n)), add(S(m), n)),
       m),
      ({n: add(S(m), n), m: add(S(m), n), k: n},
       add(S(add(S(m), n)), add(S(m), n)),
       n),
      ({n: add(S(m), n), m: add(S(m), n), k: add(S(m), n)},
       add(S(add(S(m), n)), add(S(m), n)),
       add(S(m), n)),
      ({n: S(m), m: k, k: add(S(m), n)}, add(S(k), S(m)), add(S(m), n)),
      ({n: S(m), m: m, k: add(S(m), n)}, add(S(m), S(m)), add(S(m), n)),
      ({n: S(m), m: add(S(m), n), k: m}, add(S(add(S(m), n)), S(m)), m),
      ({n: S(m), m: add(S(m), n), k: add(S(m), n)},
       add(S(add(S(m), n)), S(m)),
       add(S(m), n))],
     [({n: k, m: k, k: add(S(m), n)}, add(S(k), k), add(S(m), n)),
      ({n: k, m: m, k: add(S(m), n)}, add(S(m), k), add(S(m), n)),
      ({n: m, m: m, k: add(S(m), n)}, add(S(m), m), add(S(m), n)),
      ({n: n, m: k, k: add(S(m), n)}, add(S(k), n), add(S(m), n)),
      ({n: n, m: m, k: add(S(m), n)}, add(S(m), n), add(S(m), n)),
      ({n: S(m), m: k, k: add(S(m), n)}, add(S(k), S(m)), add(S(m), n)),
      ({n: S(m), m: m, k: add(S(m), n)}, add(S(m), S(m)), add(S(m), n))])

```python
import kdrag.theories.nat as nat

Expr = kd.Inductive("Expr")
Expr.declare("A")
Expr.declare("B")
Expr.declare("Foo", ("f1", Expr), ("f2", Expr))
Expr = Expr.create()
Foo,A,B = Expr.Foo, Expr.A, Expr.B
n,m,k = smt.Consts("n m k", Expr)
#E = EGraph()
#E.union(nat.Z + nat.Z, nat.Z)
#E.union(nat.S(nat.Z) + nat.Z, nat.S(nat.Z))
#E.union(nat.Z + nat.S(nat.Z), nat.S(nat.Z))
#E.solver.add(nat.add.defn.thm)
eunify([n,m], Foo(n,n), Foo(m,A)) 
```

    ([({n: A, m: n}, Foo(A, A), Foo(n, A)),
      ({n: A, m: A}, Foo(A, A), Foo(A, A)),
      ({n: m, m: A}, Foo(m, m), Foo(A, A))],
     [({n: A, m: n}, Foo(A, A), Foo(n, A))])

```python
(x + y) + z  ==  
```

```python
from kdrag.all import *
from kdrag.solvers.egraph import EGraph
def eunify(vs, E, t1, t2):
    todo = [(t1,t2)]
    subst = {}
    def is_var(t):
        return any(v.eq(t) for v in vs)
    while todo:
        t1, t2 = todo.pop()
        if E.is_eq(t1,t2):
            continue
        else:
            if is_var(t1):

            # It's the decompose move that needs egraph expansion.



```

      Cell In[1], line 6
        E.
          ^
    SyntaxError: invalid syntax

```python
from kdrag.all import *

Egraph = dict[int, smt.ExprRef]

def find(egraph, expr):
    while expr.get_id() in egraph:
        expr = egraph[expr.get_id()]
    return expr

def union(egraph, e1, e2):
    e1 = find(egraph, e1)
    e2 = find(egraph, e2)
    if e1.eq(e2):
        return e1
    egraph[e1.get_id()] = e2
    return e2

def rebuild(egraph):
    # Rebuild the egraph
    new_egraph = {}
    for expr in egraph.values():
        
    return new_egraph

def 

```

The brute force egraph.
bottom up ematching turns patterns into guards

could maybe use contexts as unsat cores?

ctxs : list[smt.BoolRef]

rebuild removes impossible contexts. hmhm
coalescing contexts also. Some are equivalent. Some imply the others.

for ctx in ctxs:

SMT Solvers as theories. I said that for SMT modulo SMT you can use smt as a pure theory solver.
sunsat cores communicate back.

Egraphs modulo theorie but the theory is smt. Egraph modulo SMT. Now we're getting insane. The "value" object is smtexpr. We don't have a normalizer, but we do have an equality oracle. You can still work with this.
Shostak is normalizer. Nelson-Oppen is equality oracle (slash propagator).

SMTmodel |= SMT |= Eqs

<https://microsoft.github.io/z3guide/programming/Example%20Programs/Formula%20Simplification/>
Well, there ya go.
He;'s also using model based pruning.
This makes a term bank out of the single term to be simplified. It replaces subterms with other equivalent subterms. A nice kind of semantic cse.
Whereas the eqsat approach is generating new nice subterms.

It's kind of a knob towards <https://www.pypy.org/posts/2024/07/finding-simple-rewrite-rules-jit-z3.html> or ruler but as the egraph itself. Ruler discovers non ground rules. We're discovering the egraph.

What are egraphs: Yes they are bipartite graph, a data structure.
They are models. Show z3 model.
Uninterpreted models.

Egraphs aren't complete. the "only" wya to make them complete is to have a generation process or go unification.

```python
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
```

```python
# minimal version doesn't even need union find
@dataclass
class EGraph():
    terms : dict[int, smt.ExprRef]
    solver : smt.Solver
    def __init__(self):
        self.terms = {}
        self.solver = smt.Solver()
    def add_term(self, t):
        if t.get_id() not in self.terms:
            self.terms[t.get_id()] = t
            for c in t.children():
                self.add_term(c)
    def is_eq(self, t, s):
        self.solver.push()
        self.solver.add(t != s)
        res = self.solver.check()
        self.solver.pop()
        return res == smt.unsat
    def ematch(self, vs, p):
        for ts in itertools.product(self.terms.values(), len(vs)):
            s = smt.substitute(p, *zip(vs, ts))
            for t in self.terms.values():
                if self.is_eq(t, s):
                    yield (ts, t) # maybe return s or p also. They are easily derived.?
                    break

E = EGraph()
E.add_term()
E.


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

```python
from kdrag.all import *
from dataclasses import dataclass

@dataclass
class EGraph():
    terms : dict[int, smt.ExprRef]
    uf : dict[int, int]

    def add_term(self, t):
        if t.get_id() not in self.terms:
            self.terms[t.get_id()] = t
            for c in t.get_children():
                self.add_term(c)
    def find_id(self, eid):
        while eid in self.uf:
            eid = self.uf[eid]
        return eid
    def find(self, t):
        if t.get_id() in self.terms:
            return self.terms[self.find_id(t.get_id())]
        else:
            raise ValueError(f"Term {t} not in egraph")
            #return t # maybe. Or error?
    def canon(self, t):
        args = [self.canon(c) for c in t.children()]
        return self.find(t.decl()(*args))
    def union(self, t1, t2):
        t1 = self.find(t1)
        t2 = self.find(t2)
        if t1.eq(t2):
            return t1
        self.uf[t1.get_id()] = t2.get_id()
        return t2

    
```

```python
@dataclass
class EGraph():
    terms : dict[int, smt.ExprRef]
    uf : dict[int, int | smt.ExprRef] # constructor egraph. int represents keep going, expref means is canonical.
    
```

```python
from kdrag.all import *

Egraph = dict[smt.ExprRef, smt.ExprRef]

def find(egraph, expr):
    while expr in egraph:
        expr = egraph[expr]
    return expr

def union(egraph, e1, e2):
    e1 = find(egraph, e1)
    e2 = find(egraph, e2)
    if e1.eq(e2):
        return e1
    egraph[e1] = e2
    return e2

def rebuild(egraph): # hmmm.
    new_egraph = {}
    for expr in egraph.keys():
        new_expr = expr.decl()(*(find(egraph, c) for c in expr.children()))
        if new_expr.eq(expr):
            new_egraph[new_expr] = find(egraph, expr)
    return new_egraph

def rebuild(egraph):
    todo = set(egraph.keys()) | set(egraph.values())
    while todo:
        e = todo.pop()
        new_expr = e.decl()(*(find(egraph, c) for c in e.children()))
        union(egraph, new_expr, e)
    return egraph

egg = {}

a,b,c = smt.Ints('a b c')
union(egg, a, b)
union(egg, b, c)
find(egg, a)
rebuild(egg)

f = smt.Function('f', smt.IntSort(), smt.IntSort())
egg = {}
union(egg, f(a), a)
union(egg, a , f(f(f(a))))
rebuild(egg)
rebuild(egg)
rebuild(egg)

def enorm(egraph, t):
    return find(egraph, t.decl()(*[enorm(c) for c in t.children()]))



def rec_add(termbank, t):
    if t not in termbank:
        termbank.add(t)
        for c in t.children():
            rec_add(termbank, c)

def compress_termbank(termbank):
    tbank = {}
    for t in termbank:
        rec_add(tbank, enorm(egraph, t))
    return tbank   

def rebuild(egraph, termbank):
    for t in termbank:
        new_expr = t.decl()(*(find(egraph, c) for c in t.children()))
        union(egraph, new_expr, t)

```

    {f(a): a, a: f(f(f(a))), f(f(f(f(a)))): f(f(f(a)))}

```python
import kdrag.theories.int as int_

rules = [
    int_.add_assoc,
    int_.add_comm,
    int_.add_zero,
    int_.mul_assoc,
    int_.mul_comm,
    int_.mul_zero,
]
rules = [rw.rewrite_of_expr(r) for r in rules]
termbank = { a + a + a}
egraph = {}

def ematch(egraph, termbank, vs, t):
    res = []
    for ts in itertools.product(termbank, (vs)):
        subst = list(zip(vs, ts))
        t1 = enorm(egraph, smt.substitute(t, *subst))
        if t1 in termbank:
            res.append((subst, t1))
    return res

def erewrite1(egraph, termbank, rules):
    for r in rules:
        for subst, lhs in ematch(egraph, termbank, r.vs, r.lhs):
            rhs = enorm(egraph, smt.substitute(r.rhs, *subst))
            termbank.add(rhs) # recursive?
            union(egraph, lhs, rhs)




```

    ---------------------------------------------------------------------------

    NameError                                 Traceback (most recent call last)

    Cell In[23], line 25
         22     return res
         24 for r in rules:
    ---> 25     for subst, lhs in ematch(egraph, termbank, r.vs, r.lhs):
         26         rhs = enorm(egraph, smt.substitute(r.rhs, *subst))
         27         termbank.add(rhs)


    Cell In[23], line 17, in ematch(egraph, termbank, vs, t)
         15 def ematch(egraph, termbank, vs, t):
         16     res = []
    ---> 17     for ts in itertools.product(termbank, (vs)):
         18         subst = list(zip(vs, ts))
         19         t1 = enorm(egraph, smt.substitute(t, *subst))


    NameError: name 'itertools' is not defined

```python
def
```

```python
import itertools
def esolve(egraph, termbank, vs, t, s):
    res = []
    for ts in itertools.product(termbank, (vs)):
        subst = list(zip(vs, ts))
        t1 = smt.substitute(t, *subst)
        s1 = smt.substitute(s, *subst)
        if enorm(t1).eq(enorm(s1)):
            res.append(subst)
    return res

def ematch(egraph, termbank, vs, t):
    res = []
    for ts in itertools.product(termbank, (vs)):
        subst = list(zip(vs, ts))
        t1 = enorm(egraph, smt.substitute(t, *subst))
        if t1 in termbank:
            res.append((subst, t1))
    return res




```

Wow, claude is pretty good.

# sympy eunify

Unification is Equation Solving.

Go ground. Go flat
 multiset equations

Nearly flat lambda unification and slotted egraphs.

p == q ---->  [  othereqs ]

Cody and Max are kind of into KB ~ e-unify.

Wheels within wheels. We can have a KB running inside of e-unify to solve steps modulo a theory
But also we could have e-unify running inside KB to do narrowing / overlap modulo equations.
Could I actually make an implementation that reflects this tower?

subsumption and inductionless induction. What "counts" as being subsumed and implicit. Could have a theorem prover called at every resolution step.
Another example of wheels within wheels.

Syntactic unification is a nice base case.

```python
from dataclasses import dataclass
import itertools 
from typing import Optional

@dataclass
class MultiSet():
    elmts : list # sorted list
    def __init__(self, elts):
        self.elmts = sorted(elts)
    def solve(self, other):
        assert isinstance(other, MultiSet)
        if len(self.elmts) != len(other.elmts):
            return
        for p in itertools.permutations(other.elmts):
            yield zip(self.elmts, p)

@dataclass
def Var():
    # I'm mixing my styles here. This is a mutational style. Whatev.
    val : Optional[object]
    def __init__(self):
        pass
    def solve(self, other):
        if v.val is None:
            self.val = other
            yield []
        yield [(self, other)]

@dataclass
class Lit():
    val : object
    def __init__(self, val):
        self.val = val
    def solve(self, other):
        assert isinstance(other, Lit)
        if self.val == other.val:
            yield [(self.val, other.val)]
        else:
            return

class MySet():
    elmts : list
    def __init__(self, elts):
        self.elmts = sorted(elts)
    def solve(self, other):
        pass #allow repeats

list(MultiSet([1,2,3]).solve(MultiSet([3,2,1]))


```

      Cell In[10], line 28
        
        ^
    SyntaxError: incomplete input

```python
from sympy import *

f = Function('f')
x,y = symbols('x y')
solveset(f(x) - f(y), x)
solve(f(x) - f(y), x)
```

    [y]

Substitution intersection also requires unification / is unification.
Non threaded / bottom up unification needs to merge branches.

Threads:

unitary finitary inifintary and type 0. how big set of miniaml unifiers is
elemenary, with constants and general. Whether there are extra symnbols not in E.
X1 + X2 + X3 = X4
X1 + a = X4
X1 + f(X2) = X4

single vs multiple equations.

KB + eunify.

```
------------------------
kbE, kbR |- euP, euE, euS  ===> 
```

categoruy theory: find best sig. equalizer.
f . sig = g . sig
e-unification will be the same in a lawvere theory

<https://www.cs.bu.edu/fac/snyder/publications/UnifChapter.pdf> chapter from handbook
huh. wayne snyder is in boston
[Jouannaud and Kirchner 1991,
Baader and Siekmann 1994 https://dl.acm.org/doi/abs/10.5555/185705.185711

approximate unification - we can minsat the multiequations. Or consider Least squares solutions as an anlogy. Put some kind of metric on how badly an equation is viotlated rather that descirtee 0 1. maybe go neural. neural logic pgroamming. neural unification

Bottom up eunification - Guess over a database what you'll unify on.

E-unification and narrowing
HO pattern unify
Full HO unify

I've said that higher order != has syntactic lambdas. Higher order unification could maybe seen as E-unify modulo combinator equations?

Unification modulo egraphs

boolean unification

Rational tree unification. Non well founded equations. Rationals themselves as coalgebra?

most general unifier as a greatest fixed point? Greatest something.

Categorical perspectives on substitutions.
Arrows. sure. between what? Variable sets? Term sets? Something else?

Guassian elimination means two things.
Add rows. - This is more like knuth bendix. ForAll uvars and bottom up, forward chaining
isolate variable and subst. More like unify. Exists uvars and top down, back chaining

equation breakdown. We could keep the old equations in a saturation process.
sin(x) = y --> x = arcsin(y)

Unify with branching as clauses?

<https://www.cs.cmu.edu/Groups/fox/people/fp/papers/ppcp93.pdf>  Higher-Order Logic Programming as Constraint Logic Programming
flex flex pairs as constraints

e-unify via ATP
factoring rules do the analog of solving unification (?) in a prolog

```
cnf(axiom, plus(X,Y) = plus(Y,X)). % The E-ness
cnf(conjecture, ~(f(X) = g(Y))).
```

ATP already unifies E-unification with knuth bendix
facotring rules

```
t != s | u = v
----------------
   s[u] = s[v]

```

Traat chapter uses something akin to multiset knuth bendix for Ac-unify

higher order unification vs higher order atp vs lambda prolog

As awlays

I was suggesting in co-egraphs

unification modulo derivatives?
That plotkin thing
integrals?
trig?

```python
def comm_unify(vs,t1, t2):
    # todo quee is not in DNF. An and of ors...
    # Hmm. Not sufficient.
    # ok so an or of and ands
    todo = [[(t1,t2)]]
    if is_add(t):
        if is_add(s):
            if len(t.children()) = len(s.children())
                # The chilrren choices are correlated here.
                # ok, so we do need to
                # probably here we should delay this unification as long as possible
                todo = [todo.copy() + [(t[i], s[perm[i]])  for i in range(n) ] for perm in permutations(n)]
                


# unification arranged as a given clause algorithm
def given_clause_unify():

```

Ematch
As always, we should consider ematching first.
Here again we get a flavor of unification's complication anyway and having a global queue to look at is useful.
We can delay hard destructions until later
prolog freeze

## AC

AC unify is exact opposite of AC KB?
Multiset something

matrices of subsitutions. "multply" is subst composition, add is multiset combine?

## Boolean

That recent typechekcing paper flix <https://dl.acm.org/doi/10.1145/3485487> Relational nullable types with Boolean unification
<https://www.youtube.com/watch?v=BPW-92b7j7A&ab_channel=ACMSIGPLAN> fast and efficient boolean unification for hindley milner

boolean unification the sotry so far <https://www.cs.rice.edu/~javaplt/411/23-spring/NewReadings/Unfication%20Theory/Boolean-unification---The-story-so-far_1989_Journal-of-Symbolic-Computation.pdf>

Reduce to f(x) = g(x) becomes f(x) + g(x) = 0.

loweneim and booles method

## Generic Narrowing

System G
{e[u]} ==> {l = u, e[r]}
lazy paramdoulation is bruteforce
u can't be a variable
It avoids needing unification to perform narrowing.

unification modulo egraphs

Fey and Hullot
narrow

## Functional Logic Programming

<https://www.michaelhanus.de/publications/papers/PPDP25.pdf> Determinism Types for Functional Logic Programming

<https://www.curry-language.org/docs/tutorial/tutorial.pdf> curry a ttutorial introduction

<https://www.michaelhanus.de/papers/GanzingerFestschrift.pdf> from narrowing to curry

functional logic programming
<https://dl.acm.org/doi/pdf/10.1145/1721654.1721675> review article

inductively sequential
definition trees

weakly orthogonal. There is non trivial overlap but all critical pairs are immiedately good.

flattening. append(x,y) = z --> append(x,y,z) Different orderings of flattenings make different eval strategies
`t = e` :-

flp minikanren?
curry
verse

lambda flp?

narrowing
residuization\

functional logic programming.
ground flp proplog
<https://web.cecs.pdx.edu/~antoy/homepage/publications/narrowing/paper.pdf>

<https://simon.peytonjones.org/assets/pdfs/verse-conf.pdf> verse

<https://arxiv.org/pdf/2405.10801>  The Relational Machine Calculus

<https://maude.lcc.uma.es/manual271/maude-manualch16.html> Narrwoing maude
<https://maude.lcc.uma.es/maude31-manual-html/maude-manualch15.html>
[77]   Joseph Goguen and José Meseguer. Eqlog: Equality, types and generic modules for logic programming.
]   Michael Hanus. The integration of functions into logic programming: From theory to practice
 José Meseguer. Multiparadigm logic programming
] James R. Slagle. Automated Theorem-Proving for Theories with Simplifiers
Commutativity, and Associativity

 <https://dl.acm.org/doi/abs/10.1145/1016850.1016865>  Implementing functional logic languages using multiple threads and stores

 <https://pdxscholar.library.pdx.edu/cgi/viewcontent.cgi?article=7501&context=open_access_etds>  Implementing a Functional Logic Programming Language via the Fair Scheme

What about a functional logic programming approach to marshall? We had these taylor series approximations. It's kind of intuitiopnsitc in some sense. Maybe bring in unification modulo polynomials? Modulo polynomial inequalities?

sergio antoy <https://web.cecs.pdx.edu/~antoy/>
michael hanus

<https://web.cecs.pdx.edu/~antoy/homepage/theses/A_Peters.pdf>  The Basic Scheme for the Evaluation of Functional Logic Programs . relatively simple ocaml

cloning
needed narrowing - <https://www.informatik.uni-kiel.de/~mh/papers/JACM00.pdf>
bubbling
pull tabbing

goedel

maybe kics is the way to go.

Could be fun to mix evaluation a la unfold with narrowing via rules. That's the idea right?
Or evaluation via reify + narrow.

```python
def rewrite_search(t, rules):
    seen = {}

```

```python
from kdrag.all import *
import kdrag.rewrite as rw

#def ground(vs, t): / is_value?
# 


# could do a rewriting
#  search similarly you know.
def flp(vs, t, rules):
    rules = [
        rule if isinstance(rule, rw.RewriteRule) else rw.rewrite_of_expr(rule)
        for rule in rules
    ]
    subst = {}
    todo = [(vs, t, subst)] # could have mutiple t?
    while todo:
        vs,t,subst = todo.pop()
        progress = False
        for rule in rules:
            rule = rule.freshen()
            narrows = rw.all_narrows(vs + rule.vs, t, rule.lhs, rule.rhs)
            if len(narrows) != 0: # no. I don't want this just because 
                progress = True
            for t1, subst1 in rw.all_narrows(vs, t, rule.lhs, rule.rhs):
                # combine subst and subst1
                # reduce vs maybe
                # maybe yield here if reach some condition
                todo.append((vs, t1, subst | subst1))
        if not progress:
            yield vs, t, subst

import kdrag.theories.nat as nat
rules = [
    nat.add_zero,
    nat.add_succ,
]

```

COuld be fun to table too. Variant tabling.

```python
from kdrag.all import *
def prolog(vs0 : list[smt.ExprRef], goals : smt.BoolRef, rules : list[rw.RewriteRule]):
    rules = [
        rule if isinstance(rule, rw.Rule) else rw.rule_of_expr(rule)
        for rule in reversed(rules)
    ]
    todo = [(vs0, goals, {})]
    while todo:
        vs, goals, subst = todo.pop()
        if len(goals) == 0:
            yield vs, {k : t for k,t in subst.items() if any(k.eq(v) for v in vs0)}
            continue
        else:
            goal = goals.pop()
            if smt.is_true(goal):
                todo.append((vs, goals, subst))
            elif smt.is_false(goal):
                continue
            elif smt.is_and(goal):
                goals.extend(reversed(goal.children()))
                todo.append((vs, goals, subst))
            elif smt.is_or(goal):
                for child in goal.children():
                    newgoals = goals + [child]
                    todo.append((vs, newgoals, subst))
            else:
                for rule in rules:
                    rule = rule.freshen()
                    vs1 = vs + rule.vs
                    subst1 = kd.utils.unify(vs1, rule.conc, goal)
                    if subst1 is None:
                        continue
                    else:
                        newgoals = goals + [smt.substitute(rule.hyp, *subst1.items())]
                        newsubst = {**{k : smt.substitute(v, *subst1.items()) for k,v in subst.items()}, **subst1}
                        newvs = list(set(vs1) - set(subst1.keys()))
                        todo.append((newvs, newgoals, newsubst))

import kdrag.theories.list as list_
import kdrag.theories.nat as nat
ListInt = list_.List(smt.IntSort())
x,y,z = smt.Ints("x y z")

x,y,z = smt.Consts("x y z", nat.Nat)
plus = smt.Function("plus", nat.Nat, nat.Nat, nat.Nat, smt.BoolSort())
rules = [
kd.QForAll([y], plus(nat.Z, y, y)),
kd.QForAll([x,y,z], smt.Implies(
    plus(x, y, z), 
    plus(nat.S(x), y, nat.S(z))
))
]
print(list(prolog([x,y], [plus(x, y, nat.S(nat.Z))], rules)))
print(list(prolog([x,y], [plus(x, y, nat.S(nat.Z))], rules)))
print(list(prolog([x,y], [plus(nat.Z, nat.Z, nat.S(nat.Z))], rules)))
import itertools
print(list(itertools.islice(prolog([x,y,z], [plus(x, y, nat.S(z))], rules), 4)))

```

    [([], {y: S(Z), x: Z}), ([], {x: S(Z), y: Z})]
    [([], {y: S(Z), x: Z}), ([], {x: S(Z), y: Z})]
    []
    [([z], {y: S(z), x: Z}), ([y], {x: S(Z), z: y}), ([y], {x: S(S(Z)), z: S(y)}), ([y], {x: S(S(S(Z))), z: S(S(y))})]

```python
def datalog(facts, rules):
    db = {fact.get_id() : fact for fact in facts}
    rules = 

```

```python
%%file /tmp/hello.curry

{-# LANGUAGE NoImplicitPrelude #-}
data Nat = Z | S Nat
data MyBool = False | True
-- Addition on natural numbers.
add :: Nat -> Nat -> Nat
add Z n = n
add (S m) n = S (add m n)
-- Less-or-equal predicate on natural numbers.
leq :: Nat -> Nat -> MyBool
leq Z _ = True
leq (S _) Z = False
leq (S x) (S y) = leq x y


just_doit = 3


```

    Overwriting /tmp/hello.curry

```python
!kics2 :eval just_doit :quit
```

    /bin/bash: line 1: kics2: command not found

```python
%%file /tmp/hello.curry
main = IO.println "hello world"
```

    Overwriting /tmp/hello.curry

```python
%%file /tmp/hello.curry
main = print "hello world"
```

    Overwriting /tmp/hello.curry

```python
! runcurry /tmp/hello.curry
```

cypm install runcurry

```python

```
