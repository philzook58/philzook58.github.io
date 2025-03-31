---
title: A Small Prolog on the Z3 AST
date: 2025-03-31
---

One nice thing about Knuckledragger <https://github.com/philzook58/knuckledragger> is that I have built a raft of little functionality such that now I can rip out cute little examples.

The main thing that I have ready to go here is an implementation of unification.  <https://www.philipzucker.com/unify/> <https://www.philipzucker.com/ho_unify/>
That combined with term orderings are the main annoying fiddly things you need to build little versions of many automated reasoning algorithms.

Prolog is many things. It is a particular strategy on resolution. <https://en.wikipedia.org/wiki/SLD_resolution>

My interpreter starts with a set of goals (implicitly conjoined) that you want to solve and a list of `vs` to consider to be unification variables. I have been using the style of explicitly maintainng which constants I consider variables. I could use z3's de bruijn Var, but this wouldn't work right in higher order situations.

The state of the interpreter is a list of states. The outer list represents possible backtrackings you may need to try. The inner list is the thing closer to a normal stack and state in another language. The "stack" is a list of goals you still need to discharge in order to succeed.  This goal stack is also basically a continuation data structure <https://en.wikipedia.org/wiki/Continuation> . The "state" is the current substitution in this branch
That logic programming has these two stack structures is what makes it confusing sometimes when comparing against non logic programming interpreters. I have implemented this is a super brute force inefficient way. The goals share a lot of substructure, so we could factor together these two lists into a single structure. But then we also need to rip apart substitutions. Eh.

The interpreter loop is:

- We pop the current goals of the todos
- break down the top goal if we can
- Otherwise try to apply each rule in our ruleset

You apply a rule by unifying it's head with the current goal. That changes the current substitution.

```python
import kdrag.smt as smt
import kdrag.rewrite as rw
import kdrag as kd
from typing import Sequence

def prolog(
    vs0: list[smt.ExprRef],
    goals: list[smt.BoolRef],
    rules0: Sequence[rw.Rule | smt.QuantifierRef | smt.BoolRef],
):
    """
    A small prolog interpreter. This is a generator of solutions consisting of variable list, substitution pairs.
    """
    rules = [
        rule if isinstance(rule, rw.Rule) else rw.rule_of_expr(rule) # rule_of_expr converts formulas in horn clause for to Rule tuples.
        for rule in reversed(rules0) # reversed because we will push on this list in order and I want to apply the first rules first.
    ]
    todo = [(vs0, goals, {})] # initial empty substitution
    while todo:
        vs, goals, subst = todo.pop()
        if len(goals) == 0: # nothing more to do on this branch. Success!
            yield vs, {k: t for k, t in subst.items() if any(k.eq(v) for v in vs0)}
            continue
        else:
            goal = goals.pop()
            # goal breakdown. R-sequent rules
            if smt.is_true(goal): # trivial
                todo.append((vs, goals, subst))
            elif smt.is_false(goal): # failure
                continue
            elif smt.is_and(goal): # break down into it's pieces and put on goals
                goals.extend(reversed(goal.children()))
                todo.append((vs, goals, subst))
            elif smt.is_or(goal):  # two different branches to try.
                for child in goal.children():
                    newgoals = goals + [child]
                    todo.append((vs, newgoals, subst))
            else:
                for rule in rules: # try each rule. Doing this eagerly is bit odd, but simple.
                    rule = rule.freshen()  # freshen the vars in the rule. inefficient.
                    vs1 = vs + rule.vs
                    subst1 = kd.utils.unify(vs1, rule.conc, goal)
                    if subst1 is None: # did not unify
                        continue
                    else:
                        newgoals = goals + [smt.substitute(rule.hyp, *subst1.items())]
                        newsubst = {
                            **{
                                k: smt.substitute(v, *subst1.items())
                                for k, v in subst.items()
                            },
                            **subst1,
                        }
                        newvs = list(set(vs1) - set(subst1.keys()))
                        todo.append((newvs, newgoals, newsubst))

```

```python
import kdrag.theories.nat as nat
x,y,z = smt.Consts("x y z", nat.Nat)
plus = smt.Function("plus", nat.Nat, nat.Nat, nat.Nat, smt.BoolSort())
rules = [
    kd.QForAll([y], plus(nat.Z, y, y)),
    kd.QForAll([x,y,z], smt.Implies(
            plus(x, y, z),
            plus(nat.S(x), y, nat.S(z))
        ))]
list(prolog([x,y], [plus(x, y, nat.S(nat.Z))], rules))
```

    [([], {y: S(Z), x: Z}), ([], {x: S(Z), y: Z})]

```python
list(prolog([x,y], [plus(x, y, nat.S(nat.Z))], rules))

```

    [([], {y: S(Z), x: Z}), ([], {x: S(Z), y: Z})]

```python
import itertools
list(itertools.islice(prolog([x,y,z], [plus(x, y, nat.S(z))], rules), 4))
```

    [([z], {y: S(z), x: Z}),
     ([y], {x: S(Z), z: y}),
     ([y], {x: S(S(Z)), z: S(y)}),
     ([y], {x: S(S(S(Z))), z: S(S(y))})]

# Bits and Bobbles

I put the code of this post here <https://github.com/philzook58/knuckledragger/blob/main/kdrag/solvers/prolog.py>

Instead of using a todo stack, could use a todo FIFO, random pick, some kind of monte carlo tree search, who knows.

Other things to do.

- implement eq
- callcc / delimitted continuations? Reflect the goal stack into the system
- tabling could be fun. store alpha invariant forms
- lambda prolog. see below.
- Add constraints. Since I'm on the z3 ast, should be easy. just mark some goals/predicates as constraints and add a constraint store (list) to the state.
- could add IO

```python
a = smt.DeclareTypeVar("a")
print = smt.Function("print", [a], smt.BoolSort())
if goal.decl().name() == "print":
    print(goal.arg(0))
```

z3 itself offers some horn clause modes. Space, a bounded model checking mode. <https://microsoft.github.io/z3guide/docs/fixedpoints/intro/>  <https://theory.stanford.edu/~nikolaj/nus.html#/sec-horn-clause-engines> You can also use define-fun-rec + proof/trace objects to embed a minikanren inside of z3 <https://www.philipzucker.com/minikanren_inside_z3/>

Real prologs include SWI <https://www.swi-prolog.org/> , scryer <https://github.com/mthom/scryer-prolog> , trealla, sicstus

Of course check out minikanren <https://minikanren.org/> Minikanren sort of swaps around which branch to do next.

<https://www.metalevel.at/prolog>

<https://www.philipzucker.com/minikanren-z3py/> The spiel here is that I avoided writing my own unification by abusing z3 instead. Non unifiable branches are certainly unsat.

<https://www.cl.cam.ac.uk/~jrh13/atp/OCaml/prolog.ml>

[a python interpreter](https://github.com/photonlines/Python-Prolog-Interpreter)

<https://curiosity-driven.org/prolog-interpreter>

Prolog and es6 generators <https://curiosity-driven.org/prolog-interpreter>

<https://news.ycombinator.com/item?id=2152570>

<https://cs.stackexchange.com/questions/6618/how-to-implement-a-prolog-interpreter-in-a-purely-functional-language>

[andrej bauer's pl zoo prolog](http://plzoo.andrej.com/language/miniprolog.html)

[1985 pascal design and implementation of prolog interpreter](https://core.ac.uk/download/pdf/228674394.pdf)

## a lark parser

```python
import kdrag as kd
import kdrag.smt as smt
import lark
import kdrag.rewrite as rw
from typing import Sequence
import sys

grammar = r"""
    start: _statement*

    _statement: fact
             | rule
             | query

    fact: predicate "."
    rule: predicate ":-" predicate_list "."
    query: "?-" predicate_list "."

    predicate_list: predicate ("," predicate)* // inlined

    predicate: IDENTIFIER "(" term_list? ")"
    term_list: term ("," term)* // inlined

    term: IDENTIFIER    -> const          // constants or functors
        | VARIABLE      -> var          // variables
        | IDENTIFIER "(" term_list ")" -> fun_app  // recursive terms (e.g., s(X))

    VARIABLE: /[A-Z][A-Za-z0-9_]*/  // Variables start with uppercase
    IDENTIFIER: /[a-z][A-Za-z0-9_]*/  // Constants and function names start with lowercase

    %import common.WS
    %ignore WS
"""

Term = smt.DeclareSort("Term")


def interp_term(t: lark.Tree) -> smt.ExprRef:
    token = t.data
    if token == "const":
        return smt.Const(t.children[0], Term)
    elif token == "var":
        return smt.Const(t.children[0], Term)
    elif token == "fun_app":
        args = t.children[1].children
        sortlist = [Term] * (len(args) + 1)
        f = smt.Function(t.children[0], *sortlist)
        return f(*[interp_term(a) for a in args])
    else:
        raise ValueError(f"Unexpected term {t}")


def interp_pred(t: lark.Tree) -> smt.BoolRef:
    assert t.data == "predicate"
    name = t.children[0]
    args = [interp_term(a) for a in t.children[1].children]
    return smt.Function(name, *([Term] * len(args)), smt.BoolSort())(*args)


def get_vars(e: smt.ExprRef) -> list[smt.ExprRef]:
    todo = [e]
    res = set()
    while todo:
        e = todo.pop()
        if smt.is_const(e) and e.decl().name()[0].isupper():
            res.add(e)
        elif smt.is_app(e):
            todo.extend(e.children())
        else:
            raise ValueError(f"Unexpected expression {e}")
    return list(res)


def interp(
    t: lark.Tree,
) -> tuple[
    list[smt.BoolRef | smt.QuantifierRef],
    list[tuple[list[smt.ExprRef], list[smt.BoolRef]]],
]:
    assert t.data == "start"
    clauses = []
    queries = []
    for stmt in t.children:
        if stmt.data == "fact":
            e = interp_pred(stmt.children[0])
            vs = get_vars(e)
            if len(vs) == 0:
                clauses.append(interp_pred(stmt.children[0]))
            else:
                clauses.append(smt.ForAll(vs, e))
        elif stmt.data == "rule":
            head = interp_pred(stmt.children[0])
            predlist = stmt.children[1]
            assert predlist.data == "predicate_list"
            body = [interp_pred(p) for p in stmt.children[1].children]
            vs = list(set(get_vars(head)) | set().union(*(get_vars(p) for p in body)))
            if len(vs) == 0:
                clauses.append(smt.Implies(smt.And(*body), head))
            else:
                clauses.append(kd.QForAll(vs, smt.And(*body), head))
        elif stmt.data == "query":
            goals = [interp_pred(p) for p in stmt.children[0].children]
            vs = list(set().union(*(get_vars(g) for g in goals)))
            queries.append((vs, goals))
        else:
            raise ValueError(f"Unexpected statement {stmt}")
    return clauses, queries


parser = lark.Lark(grammar, start="start", parser="lalr")

def run_string(s: str):
    """
    Run a Prolog-like string and return the results.

    >>> run_string("plus(z, Y, Y). plus(s(X), Y, s(Z)) :- plus(X, Y, Z). ?- plus(X, Y, s(z)).")
    [([], {Y: s(z), X: z}), ([], {X: s(z), Y: z})]
    """
    tree = parser.parse(s)
    clauses, queries = interp(tree)
    for vs, goals in queries:
        if len(goals) == 0:
            continue
        return list(prolog(vs, goals, clauses))


if __name__ == "__main__":
    with open(sys.argv[1]) as f:
        print(run_string(f.read()))
```

## Lambda prolog

Could push no escape check until later.

Oh. Maybe I never did or never lifted HO unify out of the blog post?

```python
import kdrag.smt as smt
import kdrag.rewrite as rw
import kdrag as kd
from typing import Sequence

def lamprolog(
    vs0: list[smt.ExprRef],
    goals: list[smt.BoolRef],
    rules0: Sequence[rw.Rule | smt.QuantifierRef | smt.BoolRef],
):
    rules = [
        rule if isinstance(rule, rw.Rule) else rw.rule_of_expr(rule) # rule_of_expr converts formulas in horn clause for to Rule tuples.
        for rule in reversed(rules0) # reversed because we will push on this list in order and I want to apply the first rules first.
    ]
    todo = [({v : [] for v in vs0}, [], goals, {})] # initial empty substitution
    while todo:
        vs, sig, goals, subst = todo.pop()
        if len(goals) == 0: # nothing more to do on this branch. Success!
            yield vs, {k: t for k, t in subst.items() if any(k.eq(v) for v in vs0.keys())}
            continue
        else:
            goal = goals.pop()
            # goal breakdown. R-sequent rules
            if smt.is_true(goal): # trivial
                todo.append((vs, goals, subst))
            elif smt.is_false(goal): # failure
                continue
            elif smt.is_and(goal): # break down into it's pieces and put on goals
                goals.extend(reversed(goal.children()))
                todo.append((vs, goals, subst))
            elif smt.is_or(goal):  # two different branches to try.
                for child in goal.children():
                    newgoals = goals + [child]
                    todo.append((vs, newgoals, subst))
            elif smt.is_eq(goal):
                subst1 = kd.unify(vs, goal.arg(0), goal.arg(1))  # try to unify the two sides.
                if subst1 is None:  # did not unify
                    continue
                else:
                    # apply the substitution
                    newsubst = {
                        **{
                            k: smt.substitute(v, *subst1.items())
                            for k, v in subst.items()
                        },
                        **subst1,
                    }
                    newvs = {**vs}
                    for v in subst1.keys():
                        if v in newvs:
                            del newvs[v]
                    todo.append((newvs, goals, newsubst))
            elif isinstance(goal, smt.QuantifierRef):
                if goal.is_exists():
                    vs1, body = kd.utils.open_binder(goal)
                    todo.append((vs + vs1, goals + [body], subst))
                elif goal.is_forall():
                    vs1, body = kd.utils.open_binder(goal)
                    todo.append(({v : bs + vs1 for v,bs in vs.items()}, sig + vs1, goals + [body], subst))
            else:
                for rule in rules: # try each rule. Doing this eagerly is bit odd, but simple.
                    rule = rule.freshen()  
                    vs1 = vs + rule.vs
                    # could do L sequent rules here

                    subst1 = kd.utils.unify(vs1, rule.conc, goal)
                    if subst1 is None: # did not unify
                        continue
                    else:
                        # escape check
                        if any(kd.utils.occurs(b, t) for v,t in subst1.items() for b in vs[v]):
                            continue
                        else:
                            newgoals = goals + [smt.substitute(rule.hyp, *subst1.items())]
                            newsubst = {
                                **{
                                    k: smt.substitute(v, *subst1.items())
                                    for k, v in subst.items()
                                },
                                **subst1,
                            }
                            newvs = {**vs}
                            for v in subst1.keys():
                                del newvs[v]
                            todo.append((newvs, newgoals, newsubst))
```

# narrowing

Narrowing is rewriting where you use unification instead of pattern matching. I already implemented narrowing basically in my knuth bendix post.

Needed narrowing might be better. The started of an e-unifier?

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
