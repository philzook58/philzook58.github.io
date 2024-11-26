---
title: Ground Lambda Prolog
date: 2024-11-25
---


Today, I thought I'd be writing a [lambda prolog](https://en.wikipedia.org/wiki/%CE%9BProlog) interpreter. While trying to explain what it's doing, I got kind of mired in some other interesting ideas.

Prolog is a logic programming language. It's two most interesting features are built in backtracking search and unification. These combined can make for some powerful party tricks.

Unification is kind of a mess I think and I try to avoid it. Unification is a way to be lazy at certain spots about exactly what ground term you're talking about. Terms with unification variables are kind of an abstract domain for representing possibly infinite sets of terms and unification is a way to form intersections of the sets.

So it is interesting that you can make prolog variations that just cuts out support for the formula that require unification or replaces the unification mechanism with a weaker but simpler term guessing mechanism. This weaker mechanism is pretty incomplete, but I think prolog+unification is also effectively incomplete and only has some character of completeness because we design our programs and axiomatizations around it's strengths and avoid its weaknesses.

# Proplog

What makes prolog a logic programming language is that prolog execution can also be seen as proof search. Indeed, prolog's origin live in noticing strategies for resolution theorem proving with good implementation properties (maybe. I think also it came out of some wacky linguistic grammar stuff <https://arxiv.org/pdf/2201.10816>).

You can write a prolog interpreter in a style where it mirrors the rules of a sequent calculus. I use the book "Programming in Higher Order Logic" by Nadathur and Miller, a text I find myself returning to and gaining something repeatedly.

I've seen a restricted form of prolog that only has propositions referred to as Proplog. See for example chapter 1 in Maiaer and Warren computing with logic. I think this is an appropriate name for this subset of horn clauses, even though I don't persay require atomic propositions.

A few random koans about the distinction between goals and programs.

- Goals are the things entered at the prolog command line at `?-`. They are formula we are trying to prove.
- Programs are the clauses written in prolog files. They are axioms.
- Goals are on the right of the sequent `|-` and programs are on the left `|-`
- It is important to note a strong distinction between goals and programs/axioms. Goals come from the top, programs come from the bottom.
- Programs are the things that can be used in forward inference, goals do backward inference.
- Variables in programs are universally quantified, variables in goals are implicitly existentially quantified.
- Goals are queries, programs are answers.
- Goals are negative and programs are positive (or vice versa. Depends how you define negative and positive).
- In an LCF style, programs are of type `thm` and goals are of type `fm`.

The right rules of the sequent calculus break down goals.

- If our goal is `true` we are done
- if our goal is `A /\ B` we can break it down into two required goals `A` and `B`
- if our goal is `A \/ B` we can break it down into two possible `A` or `B`
- otherwise, try to use our axioms

![](/assets/right_harrop.png)

The left rules break down a focused program formula.

- If our program matches our goal, we're good. This is a `refl` or `ax` rule
- if our program is `A /\ B` we can break it down into using either `A` or `B`
- if our program is `A -> B`, if we can use it to prove the current goal using `B` if we can prove the new goal `A`.

![](/assets/left_harrop.png)

I'm using z3 as a handy logical syntax tree.

Proplog has the even more restricted goal and program formula describe by this grammar

```
G ::= True | A | G ∧ G | G ∨ G
D ::= A | G ⊃ D | D ∧ D
```

The python code reflects the sequent calculus rules quite directly. It returns None when it fails and `True` when it succeeds. Failure is not intended to mean that the goal is false, just that we failed to prove it.

```python
from z3 import *

def horn(ps : list[z3.BoolRef],g : z3.BoolRef) -> bool:
    """ program clauses ps and goal g"""
    def right(g):
        #print("right", g)
        if is_true(g):
            return True
        if is_and(g): # R and
            return all(right(c) for c in g.children())
        if is_or(g): # R or
            return any(right(c) for c in g.children())
        elif is_app(g) and not is_true(g) and not is_false(g) and not is_or(g): # decide rule
            return decide(g)

    def decide(g):
        """ Try using one of the axioms"""
        return any(left(p,g) for p in ps)

    def left(p, g):
        #print("left", p, g)
        if p.eq(g): # initial
            return True
        elif is_and(p):
            return any(left(c, g) for c in p.children())
        elif is_implies(p):
            return left(p.arg(1), g) and right(p.arg(0))
        
    return right(g)

a,b,c,d = Bools('a b c d')
ps = [a,
      Implies(a, b),
      Implies(Or(a,a), b),
      Implies(And(a,b),c)]

assert horn(ps, c) 
assert not horn(ps, d)
assert horn(ps, Or(b,d))
assert horn(ps, And(a,c))
assert not horn(ps, And(a,d))
```

# Ground Prolog and Magic Terms

Ok, but we'd like to extend the formulas we can treat. Actual prolog can handle `forall` quantifiers in programs clauses and `exists` quantifier in goals. They are the implicit binders of the unification variables.

In Nadathur and Miller, they introduce this not using unification, but instead magicking up the right term when you need to open a binder. I kind of like this.

The horn procedure now takes a list of magic terms to try when a binder needs to be instantiated. It's a cute brute force method. `magic` could also perhaps be an infinite generator or just the signature (a list of `FuncDeclRef`), with a built in generator inside of `horn` of all possible terms.

```
G ::= True | A | G ∧ G | G ∨ G | ∃τ x G
D ::= A | G ⊃ D | D ∧ D | ∀x, D
```

```python
def horn(ps, g, magic):
    def right(g):
        if is_true(g):
            return True
        elif is_and(g): # R and
            return all(right(c) for c in g.children())
        elif is_or(g): # R or
            return any(right(c) for c in g.children())
        elif is_app(g) and not is_true(g) and not is_false(g) and not is_or(g):
            return decide(g)
        elif is_quantifier(g) and g.is_exists():
            # get all well typed magic terms
            return any(right(substitute_vars(g.body(), t)) for t in magic if t.sort() == g.var_sort(0))
            #for t in magic:
            #    if t.sort() == g.var_sort(0)
            #        if right(substitute_vars(g.body(), t))

    def decide(g):
        return any(left(p,g) for p in ps)

    def left(p, g):
        if p.eq(g): # initial
            return True
        elif is_and(p): # left and
            return any(left(c, g) for c in p.children())
        elif is_implies(p): # left implies
            return left(p.arg(1), g) and right(p.arg(0))
        elif is_quantifier(p) and p.is_forall():
            return any(left(substitute_vars(p.body(), t), g) for t in magic if t.sort() == p.var_sort(0))
        
    return right(g)


succ = Function("succ", IntSort(), IntSort())
zero = IntVal(0)
add = Function("add", IntSort(), IntSort(), IntSort(), BoolSort()) 
x,y, z = Ints("x y z")
magic = [zero, succ(zero), succ(succ(zero)), succ(succ(succ(zero)))]
ps = [
      ForAll([x], add(0,x,x)),
      ForAll([x], ForAll([y], ForAll([z], Implies(add(x, y, z), add(succ(x), y, succ(z))))))]

assert horn(ps, add(0, 0, 0), magic)
assert horn(ps, add(succ(zero), zero, succ(zero)), magic)
assert not horn(ps, add(succ(zero), zero, zero), magic)
assert horn(ps, Exists([x], add(zero, succ(zero), x)), magic)
assert horn(ps, Exists([x], add(zero, zero, x)), magic)
assert not horn(ps, Exists([x], add(zero, zero, succ(x))), magic)

# an query exposed on the outside to return a "substitution"
for t in magic:
    if horn(ps, add(t, zero, succ(zero)), magic):
        print(t)

```

## Going Harrop

Really, it is an orthogonal concern to add the ability to have `forall` and `implies` in goal clauses to make them harrop-y.

This version is both weaker and stronger than horn clauses. We support the fancy extra features of harrop without the quantifer support that prolog usually has (and is treated typically via unification variables). I think that's kind of interesting.

We can see that our formula has two new forms in goals compared to proplog but not the pieces that horn added

```
G ::= True | A | G ∧ G | G ∨ G | D ⊃ G | ∀x G
D ::= A | G ⊃ D | D ∧ D
```

```python
def harrop(ps, g):
    def right(ps, g):
        if is_true(g):
            return True
        elif is_and(g): # R and
            return all(right(ps, c) for c in g.children())
        elif is_or(g): # R or
            return any(right(ps, c) for c in g.children())
        # NEW:
        elif is_implies(g):
            return right([g.arg(0)] + ps, g.arg(1))
        elif is_quantifier(g) and g.is_forall():
            v = FreshConst(g.var_sort(0))
            return right(ps, substitute_vars(g.body(), v))
        # END NEW
        elif is_app(g):
            return decide(ps, g)


    def decide(sig, ps, g):
        return any(left(ps,p,g) for p in ps)

    def left(ps, p, g):
        if p.eq(g): # initial
            return True
        elif is_and(p): # left and
            return any(left(c, g) for c in p.children())
        elif is_implies(p): # left implies
            return left(p.arg(1), g) and right(p.arg(0))
        
    return right(ps, g)
```

### Full Ground Harrop

We can combine the ability to open up binders that need guess by allowing the magic term generator to take a parameter of the current eigenvariables in scope.
Eigenvariables do not escape because they aren't available to construct magic terms and the terms aren't returned.
Occurs checks aren't a thing because we build concrete terms and not partially instantiated terms or substitutions.

```
G ::= True | A | G ∧ G | G ∨ G | ∃τ x G | D ⊃ G | ∀x G
D ::= A | G ⊃ D | D ∧ D | ∀x D
```

```python
def harrop(ps, g, magic):
    def right(sig, ps, g):
        if is_true(g):
            return True
        elif is_and(g): # R and
            return all(right(sig, ps, c) for c in g.children())
        elif is_or(g): # R or
            return any(right(sig, ps, c) for c in g.children())
        elif is_app(g) and not is_true(g) and not is_false(g) and not is_or(g):
            return decide(ps, g)
        elif is_quantifier(g) and g.is_exists():
            # get all well typed magic terms
            return any(right(sig, ps, substitute_vars(g.body(), t)) for t in magic(sig) if t.sort() == g.var_sort(0))
        elif is_implies(g):
            return right([g.arg(0)] + ps, g.arg(1))
        elif is_quantifier(g) and g.is_forall():
            v = FreshConst(g.var_sort(0))
            return right(sig + [v], ps, substitute_vars(g.body(), v))

    def decide(sig, ps, g):
        return any(left(sig,ps,p,g) for p in ps)

    def left(sig, ps, p, g):
        if p.eq(g): # initial
            return True
        elif is_and(p): # left and
            return any(left(c, g) for c in p.children())
        elif is_implies(p): # left implies
            return left(p.arg(1), g) and right(p.arg(0))
        elif is_quantifier(p) and p.is_forall():
            return any(left(substitute_vars(p.body(), t), g) for t in magic(sig) if t.sort() == p.var_sort(0))
        
    return right([], ps, g)
```

# Bits and Bobbles

It is interesting and perhaps informative to consider how much prolog is left if you cut out the unification.

From a proof search perspective, when you open a existential binder in a goal or use a universally quantified axiom, the simplest thing to do would to just to have the term in hand at that moment (the `exists` tactic vs the `eexists` tactic). Unification let's you delay that choice and use further search to prune it down. It's some kind of bizarre time traveling, sending information back in time, and entangled across branches of your search space. It sucks.

Yea, I dunno.

We could use a z3 solve maybe for magic. If e is a fresh const of the needed type.

<https://www.philipzucker.com/datalog-theorem-harrop/> Datalog as a Theorem Prover: Harrop Clauses-lite

<https://www.philipzucker.com/harrop-checkpoint/>  Checkpoint: Harrop Clauses and Scoped Dynamic Databases in Regular Prolog

Ok, fine. so how do you add unification

subst plays the role of magic.

We  represented  magic as concrete terms, but it could have been data on how to generate them
Like the signature
magic could have been [succ, ]

But subtitutions are also kind of data not too disimilar from a method to genraete terms.
We're unifying for the term generator, synthesizing the term generator.
A substitution takes in useful terms (as the vars) and outputs new useful terms with those filled in.

It needs to time travel. It learns constraints about how to generate terms only after it needs them / during usage of them.

could go down into term, discover, then finish out the actual proof with grounded term.
return constraints.
return obligations
kind of feels like tactics, lenses, dialectica.
We need an equational proof at leaves. p.eq(g)

,agic could be allowed to have anything

coroutining on eq and magic

If we make eq a thing

Adding built in equality connective to nadathur and miller. Huh. They don't treat it really.

focusing and selection functions.....

proof rules for equality... like what? congreunce axioms?
Multiple baked in notions of equality? z3 ast won't nicely support that

selection is more like goal reordering.
Take off smallest goal, biggest, etc.

The "carried" egraph and unification modulo egraphs.
sig, programs, ground_eqs |- goal

could push and pop out of egraph.

sig, P, chr_facts, ground_eqs |- goal

chr has a notion of forward propagation.

If I want bog standard equality saturation in there (and I probably shouldn't because it'll be super add hoc)
I should consider how to have datalog in there. CHR already is a datalog.

sig, Prologrules, datalogrules, ground_facts |- goal

backtrack datalog. Kind of fun. Again, this is basically a subset of chr. Purely logical semantics though which is nice.

If I willing to consider KB prolog. What about resolution prolog.

 , Res_db |- goal

 Res_db saturates and receives new facts and rules from backhainig goal possibly.
 Res_db orients into rules... Res_db ~ Program_db with inprocessing?

 selection and focusing...
 We don't really pick what to predicatet o focus on inside on rule. We follow nose
 It would be some kind of prioritization principle in the is_and left rule.
         elif is_and(p): # left and
            return any(left(c, g) for c in p.children())
uh no...

Focusing is picking clause out of database. That feels more similar to the given clause heuristic weights than the selection function...

resolution with splitting. split is like focus / decide?
saturation of db
db |- goal

 db1 | db2 | db3 | ~goal

 fouusing tells us how to applyi factor rather than how to apply resolution
 A | a != b
 Mmm. no. I dunno about that. All the vars are shared acorss the clause.

 lambda resolution in the lambda prolog sense

```python
# using z3 for magic
def horn(ps, g):
    def right(g):
        if is_true(g):
            return True
        elif is_and(g): # R and
            return all(right(c) for c in g.children())
        elif is_or(g): # R or
            return any(right(c) for c in g.children())
        elif is_app(g) and not is_true(g) and not is_false(g) and not is_or(g):
            return decide(g)
        elif is_quantifier(g) and g.is_exists():
            t = FreshConst(g.var_sort(0))
            s = Solver()
            s.add(t == t)
            while s.check() != unsat:
                m = s.model()
                if right(substitute_vars(g.body(), m.eval(t))):
                    return True
                s.add(t != m.eval(t))

    def decide(g):
        return any(left(p,g) for p in ps)

    def left(p, g):
        if p.eq(g): # initial
            return True
        elif is_and(p): # left and
            return any(left(c, g) for c in p.children())
        elif is_implies(p): # left implies
            return left(p.arg(1), g) and right(p.arg(0))
        elif is_quantifier(p) and p.is_forall():
            return any(left(substitute_vars(p.body(), t), g) for t in magic if t.sort() == p.var_sort(0))
        
    return right(g)
```

## Fancier Equality

In a sense from the get go we built a ground lambda prolog, because z3 terms can have lambdas in them just fine.

But, as I noticed previously, the built in syntactic equality `p.eq(g)` doesn't even recognize alpha equivalence. <https://www.philipzucker.com/ho_unify/>

So we can replace the equality check with something fancier in our `left` rules.

We can return constraints or thread them.

<https://www.philipzucker.com/minikanren-z3py/> here I used z3 disequality unsat checks to replace unification.

```python
def horn(ps : list[z3.BoolRef],g : z3.BoolRef) -> bool:
    def right(g):
        if is_true(g):
            return True
        if is_and(g): # R and
            return all(right(c) for c in g.children())
        if is_or(g): # R or
            return any(right(c) for c in g.children())
        elif is_app(g) and not is_true(g) and not is_false(g) and not is_or(g): # decide rule
            return decide(g)

    def decide(g):
        """ Try using one of the axioms"""
        return any(left(p,g) for p in ps)

    def eq(p,g):
        s = Solver()
        s.add(p != g)
        return s.check() == unsat

    def left(p, g):
        if eq(p,g): # initial
            return True
        elif is_and(p):
            return any(left(c, g) for c in p.children())
        elif is_implies(p):
            return left(p.arg(1), g) and right(p.arg(0))
        
    return right(g)
```

returning junk

we can thread context or not

```python
import itertools

def horn(ps : list[z3.BoolRef],g : z3.BoolRef) -> bool:
    def right(ctx, g):
        if is_true(g):
            return ctx
        if is_and(g): # R and
            # just binary and supported
            for ctx1 in right(ctx, g.arg(0)):
                yield from right(ctx1, g.arg(1))
        if is_or(g): # R or
            yield from itertools.chain.from_iterable(right(ctx,c) for c in g.children())
        elif is_app(g) and not is_true(g) and not is_false(g) and not is_or(g): # decide rule
            yield from decide(g)

    def decide(g):
        """ Try using one of the axioms"""
        return yield from itertools.chain.from_iterable(left(p,g) for p in ps)

    def eq(p,g):
        s = Solver()
        s.add(p != g)
        return s.check() == unsat

    def left(p, g):
        if eq(p,g): # initial
            return True
        elif is_and(p):
            return any(left(c, g) for c in p.children())
        elif is_implies(p):
            return left(p.arg(1), g) and right(p.arg(0))
        
    return right(g)
```

Ground horn clauses.

This is so straightforward as to be easy

Maybe I could throw ex falso in there. is_false(p)

```python
def right(ps, g):
    if is_true(g):
        return True
    if is_and(g): # R and
        return all(right(ps, c) for c in g.children())
    if is_or(g): # R or
        return any(right(ps, c) for c in g.children())
    #elif is_quantifier(t) and t.is_exists(): # maybe tag with what it should be
    #    return is_goal(t.body())
    elif is_app(t) and not is_true(t) and not is_false(t) and not is_or(t):
        return decide(ps, g)

def decide(ps, g):
    return any(left(ps,p,g) for p in ps)

def left(ps, p, g):
    if p.eq(g): # initial
        return True
    # elif is_false(p): return True
    elif is_and(p):
        return any(left(ps, c, g) for c in p.children())
    elif is_implies(p):
        return left(ps, p.arg(1), g) and right(ps, p.arg(0))
    # elif is_quantifier(p) and p.is_forall():


```

```python

```

```python


```

    succ(0)

Harrop clauses.
We can add the the program database and add to the signature. magic terms may be built out of the current signature in scope.

```python

```

Lambda. Actually, we've kind of been a lambda prolog from the start.
We should replace t.eq(b) with alpha_eq

Adding theories.
We can also add a stronger notion of theories.
can the simplifier reduce simplify(b == t) -> True ?
Or a semantic s.add(b != t); s.check() == unsat?

This bizarro ground prolog is kind of fun.

Compare with minikanren on z3 blog post <https://www.philipzucker.com/minikanren-z3py/> . It's a similar game actually. I also didn't implement unification. Huh.

This has kind of got different bones though.

I could probably iomplement this for other lgoics that have a sequent calculus.

Ask a neural network to try to invent a term instead of the magic function.

In order for LLM to be useful, you need to reverse the intuition of the last 80 years of automated reasoning. You never wanted the system to need to invent anything. Now you want it to and make a big jump via then invention to overcome the slowness of the invention process.

```python

```

## Loopifying Proplog

We can systematically loopify the proplog interpreter. Turn every function into a tag

defunctionalize the continuation.

Prolog's stack has both the recursive function call structure on it and the nondeterminism in it.

Prolog continuations. edge(path(k, a, b), a, b)
Two kinds of continuations. Rule continuations (choice points) and goal/body continuations.

```python
from z3 import *

def horn(ps : list[z3.BoolRef],g : z3.BoolRef) -> bool:
    todo = [("right",  g, ("done",))]
    """ program clauses ps and goal g"""
    while todo:
        match todo.pop():
            case ("right", g, k):
                if is_true(g):
                    k(True)
                if is_and(g): # R and
                    k(all(right(c) for c in g.children()))
                if is_or(g): # R or
                    return any(right(c) for c in g.children())
                elif is_app(g) and not is_true(g) and not is_false(g) and not is_or(g): # decide rule
                    return decide(g)

    def decide(g):
        """ Try using one of the axioms"""
        return any(left(p,g) for p in ps)

    def left(p, g):
        #print("left", p, g)
        if p.eq(g): # initial
            return True
        elif is_and(p):
            return any(left(c, g) for c in p.children())
        elif is_implies(p):
            return left(p.arg(1), g) and right(p.arg(0))
        
    return right(g)
```

```python

```

```python
# defining a recofgnizer the class of horn clauses
from z3 import *
def is_goal(t : BoolRef) -> bool:
    if is_true(t):
        return True
    elif is_and(t):
        return all(is_goal(c) for c in t.children())
    elif is_or(t):
        return all(is_goal(c) for c in t.children())
    elif is_quantifier(t) and t.is_exists():
        return is_goal(t.body())
    elif is_app(t) and not is_true(t) and not is_false(t) and not is_or(t):
        return True 
    else:
        return False

def is_program(t):
    if is_implies(t):
        return is_goal(t.arg(0)) and is_program(t.arg(1))
    elif is_and(t):
        return all(is_program(c) for c in t.children())
    elif is_quantifier(t) and t.is_forall():
        return is_program(t.body())
    elif is_app(t) and not is_true(t) and not is_false(t) and not is_or(t):
        return True 
    else:
        return False
a,b,c, d = Bools('a b c d')
p = Function("p", IntSort(), BoolSort())
x = Int('x')
assert is_goal(a)
assert is_goal(a | b)
assert is_goal(a & b)
assert is_goal(Exists(x, p(x)))
assert not is_goal(ForAll(x, p(x)))
assert is_program(a)
assert not is_program(a | b)
assert is_program(a & b)
assert is_program(Implies(a, b))
assert is_program(Implies(a, b & c))
assert is_program(ForAll([x], Implies(p(x - 1) & (x > 0), p(x))))
```

```python

def horn(ps, g, subst):
    def right(g, subst):
        if is_true(g):
            return True
        elif is_and(g): # R and
            return all(right(c) for c in g.children())
        elif is_or(g): # R or
            return any(right(c) for c in g.children())
        elif is_eq(g): # break down equality goal
            pass
            unify(g.arg(0), g.arg(1), subst) # this would be standard answer
            #eunify()
            # but what if we need to prvoe the goal using equations and axioms in context?
        elif is_app(g) and not is_true(g) and not is_false(g) and not is_or(g):
            return decide(g)
        elif is_quantifier(g) and g.is_exists():
            # get all well typed magic terms
            return any(right(substitute_vars(g.body(), t)) for t in magic if t.sort() == g.var_sort(0))
            #for t in magic:
            #    if t.sort() == g.var_sort(0)
            #        if right(substitute_vars(g.body(), t))

    def decide(g, subst):
        return any(left(p,g) for p in ps)
    
    def eq(p, g, magic):
        # a whole thing
        # equaitional equality
        s = Solver()
        s.add(p != g)
        return s.check() == unsat
    # vs p == g; s.check() == sat. optimistic? incorrectness logic.
    # vs return unify(p,g,subst)  - output a proof relevant thing. Not threading would again kind of be an optimism of sorts.
    # openai.ask("Is {p} the same as {g}?"). openai.ask("how do you make {p} the same as {g}?")
    # unify modulo egraphs


    def left(p, g, subst, eq):
        if eq(p, g): # initial
            return True
        elif is_eq(p): # breaking down an equality?
            pass
            # what should go here? 
            # knuth bendix? narrowing of goal (orient and apply nondet many times) ? equatiohnal search? paramodulation?
        elif is_and(p): # left and
            return any(left(c, g) for c in p.children())
        elif is_implies(p): # left implies
            return left(p.arg(1), g) and right(p.arg(0))
        elif is_quantifier(p) and p.is_forall():
            return any(left(substitute_vars(p.body(), t), g) for t in magic if t.sort() == p.var_sort(0))
        
    return right(g)
```

The rules show magicking up `t` terms to instantiate exists in goals and foralls in programs.

```python
def right(ps, g, magic):
    if is_true(g):
        return True
    if is_and(g): # R and
        return all(right(ps, c, magic) for c in g.children())
    if is_or(g): # R or
        return any(right(ps, c, magic) for c in g.children())
    #elif is_quantifier(t) and t.is_exists(): # maybe tag with what it should be
    #    return is_goal(t.body())
    elif is_app(t) and not is_true(t) and not is_false(t) and not is_or(t):
        return decide(ps, g, magic)

def decide(ps, g, magic):
    return any(left(ps,p,g) for p in ps)

def left(ps, p, g, magic):
    if p.eq(g): # initial
        return True
    # elif is_false(p): return True
    elif is_and(p):
        return any(left(ps, c, g, magic) for c in p.children())
    elif is_implies(p):
        return left(ps, p.arg(1), g, magic) and right(ps, p.arg(0), magic)
    # elif is_quantifier(p) and p.is_forall():
```

If I don't want to thread a subst through and do eager substitution, I need access to the stack.

Resolution / datalog is knuth bendix for logic.

Prolog itself is e-unification under a logical theory. Head unification and replacement is narrowing style e-unification. Is this why set(clp) plays so badly? This is probably the FLP perspective of how to write prolog as flp.

"ground" unification. that's a funny idea. f(a) ?= f(a). yes. It is a natural question
 ground e-"unification". If you have decided rewrite system, normalize and then compare works. Or you can recurse and branch. You don't want to fully normalize lambda calc for equality checking.

```python
def horn(vs, ps, g):
    # a list of leaves
    todo = [[("right", g)]]
    while todo:
        c = todo.pop()
        match c:
            
```

## Prolog inerpreter implementation

Judgements is nice.
This is turning into more of a (otteny) theorem prover. hmmm.

Really maybe I just wanted apply

A partial proof tree has multiple hole. Searches for holes should share remainiing holes.
DOn't use just a list of all partial proof trees. Interpolate the list

<https://github.com/LPCIC/elpi/blob/master/src/compiler.ml>

<https://github.com/andrejbauer/plzoo/blob/master/src/miniprolog/solve.ml>

<https://www.philipzucker.com/harrop-checkpoint/>

```ocaml
type judgement

type trail = 
    | Choice of goal * trail (* a different goal to try and trail to reinstate (which could be more Choice ) *) 
    | 

type cont = {  next : goal;  fail: goal * cont}
type cont = {goals : judgement list; 
             fail : judgement * cont}
type cont = {
    goals : judgement list;
    success : cont;
    fail : cont
}
type cont = {
    success : (judgement * cont) option
    fail : (judgement * cont) option
}


  
```

<https://drops.dagstuhl.de/storage/01oasics/oasics-vol058_iclp2017/OASIcs.ICLP.2017.10/OASIcs.ICLP.2017.10.pdf>

<https://www.youtube.com/watch?v=SRYAMt8iQSw&list=PLJq3XDLIJkib2h2fObomdFRZrQeJg4UIW&ab_channel=softdevteamuk> Paul Tarau @ VMSS16: A Simplified Virtual Machine for Multi-Engine Prolog

A superposition of different proof trees. It's kind of like egraph / vsa / multiterm. Hmm.
a vsa list of goals.

type  goals =  Choice goal *goals | Conj goal* gone | Top
type goals = Choice of goal list *goals | Conj of goal list* goals | Top
     Choice of (goal * goals) list
If it was kind of like dnf / cnf, this is the unexpanded for of that
type goal = Disj of goal

("choice", )

What about Max's thing about dynamically recpatruing sharing in the stack.

<http://adam.chlipala.net/papers/MakamICFP18/MakamICFP18.pdf> Makam

One advantage of operating over z3 syntax tree is we get a CLP by default. CLP(SMT)
Mark some of the predicates as interpreted.

maybe a lark parser for prolog rules?

## Parsing

```python
from z3 import *
import lark.tree
# Grammar for parsing
grammar = """
    start: rule+
    rule: predicate ":-" premises "."
    predicate: ID "(" args ")"
    premises: predicate ("," predicate)*
    args: (ID | expr) ("," (ID | expr))*
    expr: ID "(" args ")"

    %import common.CNAME -> ID
    %import common.WS
    %ignore WS
"""
from lark import Lark, Transformer, Tree
parser = Lark(grammar, start='rule')
parser.parse("a(X) :- b(X), c(X).")

def interp_rule(t):
    selects = []
    froms = []
    wheres = []
    env = {}
    match Tree("rule", head, body):
    for i, premise in enumerate(body):
        row = premise.head + "_" + str(i)
        froms.append(f"{premise.head} AS {premise.head}_{i}")
        for arg in args:
        match arg enumerate(args):
            entry = row + ".x" + {i}
            case Tree("ID", name):
                if name in env:
                    wheres.append(f"{} = {env[name]})
                else:
                    selects.append(name)
            
            case
    if var in env:
        return env[var]
    else:
        env[v] = 
        return var
    match Tree("predicate", name, args):


```

    Tree(Token('RULE', 'rule'), [Tree(Token('RULE', 'predicate'), [Token('ID', 'a'), Tree(Token('RULE', 'args'), [Token('ID', 'X')])]), Tree(Token('RULE', 'premises'), [Tree(Token('RULE', 'predicate'), [Token('ID', 'b'), Tree(Token('RULE', 'args'), [Token('ID', 'X')])]), Tree(Token('RULE', 'predicate'), [Token('ID', 'c'), Tree(Token('RULE', 'args'), [Token('ID', 'X')])])])])

```python
from lark import Lark, Transformer, Tree
from z3 import *
import lark.tree
grammar = """
start: (rule | decl)+
decl: ID ":" typ "."
typ: "(" typ ")" -> typ
    | ID  -> tconst
    | typ ("->" | "→") typ -> tarrow
rule: expr ":-" premises "."
premises: expr ("," expr)*
expr : ID atom+ -> f_app 
      | atom -> atom
atom : ID 
      | "(" expr ")" -> expr 


%import common.CNAME -> ID
%import common.WS
%ignore WS
"""

example = """
term : type.
typ : type.
app : term -> term -> term.
arrow : typ -> typ -> typ.
lam : typ -> (term -> term) -> term.
typeof : term -> typ → prop.
typeof (app E1 E2) T1 :- typeof E1 (arrow T T1), typeof E2 T.

"""
#typeof (lam T1 E) (arrow T1 T2) :- (x:term -> typeof x T1 -> typeof (E x) T2).


def interp_typ(t):
    print(t)
    match t:
        case Tree("typ", [t]):
            return interp_typ(t)
        case Tree('tconst', [ID]):
            ID = str(ID)
            if ID == 'prop':
                return BoolSort()
            else:
                return DeclareSort(str(ID))
        case Tree('tarrow', [t1, t2]):
            return ArraySort(interp_typ(t1), interp_typ(t2))
     
def interp(t : Tree):
    assert t.data == 'start'
    env = {}
    rules = []
    def term(t):
        match t:
            case Tree("expr", [e]): return term(e)
            case Tree("atom", [ID]): return env[str(ID)]
            case Tree("f_app", [ID, *consts]):
                print(env[str(ID)], t)
                return env[str(ID)][tuple(term(c) for c in consts)]

    for c in t.children:
        match c:
            case Tree('decl', [ID, typ]):
                env[str(ID)] = Const(str(ID), interp_typ(typ))
            case Tree('rule', [head, premises]):
                rules.append((term(head), [term(p) for p in premises]))
    return env, rules

parser = Lark(grammar, start='start')
tree = parser.parse(example)
#print(tree.pretty())
interp(tree)


```

    Tree('tconst', [Token('ID', 'type')])
    Tree('tconst', [Token('ID', 'type')])
    Tree('tarrow', [Tree('tarrow', [Tree('tconst', [Token('ID', 'term')]), Tree('tconst', [Token('ID', 'term')])]), Tree('tconst', [Token('ID', 'term')])])
    Tree('tarrow', [Tree('tconst', [Token('ID', 'term')]), Tree('tconst', [Token('ID', 'term')])])
    Tree('tconst', [Token('ID', 'term')])
    Tree('tconst', [Token('ID', 'term')])
    Tree('tconst', [Token('ID', 'term')])
    Tree('tarrow', [Tree('tarrow', [Tree('tconst', [Token('ID', 'typ')]), Tree('tconst', [Token('ID', 'typ')])]), Tree('tconst', [Token('ID', 'typ')])])
    Tree('tarrow', [Tree('tconst', [Token('ID', 'typ')]), Tree('tconst', [Token('ID', 'typ')])])
    Tree('tconst', [Token('ID', 'typ')])
    Tree('tconst', [Token('ID', 'typ')])
    Tree('tconst', [Token('ID', 'typ')])
    Tree('tarrow', [Tree('tarrow', [Tree('tconst', [Token('ID', 'typ')]), Tree('typ', [Tree('tarrow', [Tree('tconst', [Token('ID', 'term')]), Tree('tconst', [Token('ID', 'term')])])])]), Tree('tconst', [Token('ID', 'term')])])
    Tree('tarrow', [Tree('tconst', [Token('ID', 'typ')]), Tree('typ', [Tree('tarrow', [Tree('tconst', [Token('ID', 'term')]), Tree('tconst', [Token('ID', 'term')])])])])
    Tree('tconst', [Token('ID', 'typ')])
    Tree('typ', [Tree('tarrow', [Tree('tconst', [Token('ID', 'term')]), Tree('tconst', [Token('ID', 'term')])])])
    Tree('tarrow', [Tree('tconst', [Token('ID', 'term')]), Tree('tconst', [Token('ID', 'term')])])
    Tree('tconst', [Token('ID', 'term')])
    Tree('tconst', [Token('ID', 'term')])
    Tree('tconst', [Token('ID', 'term')])
    Tree('tarrow', [Tree('tconst', [Token('ID', 'term')]), Tree('tarrow', [Tree('tconst', [Token('ID', 'typ')]), Tree('tconst', [Token('ID', 'prop')])])])
    Tree('tconst', [Token('ID', 'term')])
    Tree('tarrow', [Tree('tconst', [Token('ID', 'typ')]), Tree('tconst', [Token('ID', 'prop')])])
    Tree('tconst', [Token('ID', 'typ')])
    Tree('tconst', [Token('ID', 'prop')])
    typeof Tree('f_app', [Token('ID', 'typeof'), Tree('expr', [Tree('f_app', [Token('ID', 'app'), Tree(Token('RULE', 'atom'), [Token('ID', 'E1')]), Tree(Token('RULE', 'atom'), [Token('ID', 'E2')])])]), Tree(Token('RULE', 'atom'), [Token('ID', 'T1')])])
    app Tree('f_app', [Token('ID', 'app'), Tree(Token('RULE', 'atom'), [Token('ID', 'E1')]), Tree(Token('RULE', 'atom'), [Token('ID', 'E2')])])



    ---------------------------------------------------------------------------

    KeyError                                  Traceback (most recent call last)

    Cell In[45], line 73
         71 tree = parser.parse(example)
         72 #print(tree.pretty())
    ---> 73 interp(tree)


    Cell In[45], line 67, in interp(t)
         65             env[str(ID)] = Const(str(ID), interp_typ(typ))
         66         case Tree('rule', [head, premises]):
    ---> 67             rules.append((term(head), [term(p) for p in premises]))
         68 return env, rules


    Cell In[45], line 60, in interp.<locals>.term(t)
         58 case Tree("f_app", [ID, *consts]):
         59     print(env[str(ID)], t)
    ---> 60     return env[str(ID)][tuple(term(c) for c in consts)]


    Cell In[45], line 60, in <genexpr>(.0)
         58 case Tree("f_app", [ID, *consts]):
         59     print(env[str(ID)], t)
    ---> 60     return env[str(ID)][tuple(term(c) for c in consts)]


    Cell In[45], line 56, in interp.<locals>.term(t)
         54 def term(t):
         55     match t:
    ---> 56         case Tree("expr", [e]): return term(e)
         57         case Tree("atom", [ID]): return env[str(ID)]
         58         case Tree("f_app", [ID, *consts]):


    Cell In[45], line 60, in interp.<locals>.term(t)
         58 case Tree("f_app", [ID, *consts]):
         59     print(env[str(ID)], t)
    ---> 60     return env[str(ID)][tuple(term(c) for c in consts)]


    Cell In[45], line 60, in <genexpr>(.0)
         58 case Tree("f_app", [ID, *consts]):
         59     print(env[str(ID)], t)
    ---> 60     return env[str(ID)][tuple(term(c) for c in consts)]


    Cell In[45], line 57, in interp.<locals>.term(t)
         55 match t:
         56     case Tree("expr", [e]): return term(e)
    ---> 57     case Tree("atom", [ID]): return env[str(ID)]
         58     case Tree("f_app", [ID, *consts]):
         59         print(env[str(ID)], t)


    KeyError: 'E1'

```python

from lark import Lark, Transformer, Tree
from z3 import *
import lark.tree
# Grammar for parsing
grammar = """
start: rule+
rule: predicate ":-" premises "."
predicate: ID "(" args ")"
premises: predicate ("," predicate)*
args: (ID | expr) ("," (ID | expr))*
expr: ID "(" args ")"

%import common.CNAME -> ID
%import common.WS
%ignore WS
"""

term = DeclareSort("term")
typ = DeclareSort("typ")


# Parse and interpret Prolog rule
parser = Lark(grammar, start='start')
tree = parser.parse("typeof(app(E1, E2), T) :- typeof(E1, arrow(T, T)), typeof(E2, T).")

Tree.__match_args__ = ("data", "children")
def interp(tree):
    match tree:
        case Tree("start", rules):
            for rule in rules:
                interp(rule)
        case Tree("rule", [pred, premises]):
            print(pred)
            for premise in premises.children:
                print(premise)
        case _:
            print(tree)
interp(tree)
from IPython.display import Image, display
print(tree.pretty())
#https://stackoverflow.com/questions/4596962/display-graph-without-saving-using-pydot
Image(lark.tree.pydot__tree_to_graph(tree).create_png())

```

    Tree(Token('RULE', 'predicate'), [Token('ID', 'typeof'), Tree(Token('RULE', 'args'), [Tree(Token('RULE', 'expr'), [Token('ID', 'app'), Tree(Token('RULE', 'args'), [Token('ID', 'E1'), Token('ID', 'E2')])]), Token('ID', 'T')])])
    Tree(Token('RULE', 'predicate'), [Token('ID', 'typeof'), Tree(Token('RULE', 'args'), [Token('ID', 'E1'), Tree(Token('RULE', 'expr'), [Token('ID', 'arrow'), Tree(Token('RULE', 'args'), [Token('ID', 'T'), Token('ID', 'T')])])])])
    Tree(Token('RULE', 'predicate'), [Token('ID', 'typeof'), Tree(Token('RULE', 'args'), [Token('ID', 'E2'), Token('ID', 'T')])])
    start
      rule
        predicate
          typeof
          args
            expr
              app
              args
                E1
                E2
            T
        premises
          predicate
            typeof
            args
              E1
              expr
                arrow
                args
                  T
                  T
          predicate
            typeof
            args
              E2
              T
    





    
![png](2024-11-25-ground_lambda_prolog_files/2024-11-25-ground_lambda_prolog_37_1.png)

```python
# Convert parse tree to Z3
#transformer = PrologToZ3()
#z3_expr = transformer.transform(tree)
"""
# Transformer to interpret parsed Prolog rules
class PrologToZ3(Interpreter):
    def __init__(self):
        self.env = {"typeof": Function('typeof', term, typ, BoolSort()),
           "app": Function('app', term, term, term),
           "arrow": Function('arrow', typ,typ, typ)}
    def type_decl(self, items):
        return Function('typeof', term, typ, BoolSort())
    def const_decl(self, items):
        const_env[str(items[0])] = Function("")
    def predicate(self, items):
        func_name = str(items[0])
        args = items[1:]
        return self.env[func_name](*args)

    def ID(self, token):
        if str.isupper():
            return Const(token, typ)
        else:
            return self.env[token]
"""
```

```python
term = DeclareSort("term")
typ = DeclareSort("typ")

app = Function("app", term, term, term)
arrow = Function("arrow", typ, typ, typ)

lam = Function("lam", term, (ArraySort(term, term)), term)
typeof = Function("typeof", term, typ, BoolSort())

kd.axiom(kd.QForAll([X, Y, Z], 
                    typeof(E1, arrow(T, T1)), typeof(E2,T)
                    , arrow(app(E1, E2), T1)))


```

```python
class Rule(NamedTuple):
    vs: list[smt.ExprRef]
    head: smt.BoolRef
    body: list[smt.BoolRef]

# could use z3 datalog
# also could use z3 bounded horn clause?
def datalog(smt.ExprRef) -> :
```

## Like actuaslly doing a lambda prolog

Just sort of following my nose here.
We need to carrys the a variables currently in context.
The E variables need to hold a map to either the a vars they allow or avars they disallow for checking during

```python
def foo():
    yield 1 
    yield 2
    return 3
for x in foo():
    print(x)
```

    1
    2

```python
def right(subst,avs , ectx, db, goal):
    
```

I could reverse it

avs[a] = {e1,e2,e3} # The es that can contain a

```python
def right(subst, avs, ectx, db, goal):
    if smt.is_true(goal):
        yield subst
    elif smt.is_false(goal):
        return None
    elif smt.is_and(goal): # Rand
        for subst in right(subst, db, goal.arg(0)):
            yield from right(subst, db, goal.arg(1))
    elif smt.is_or(goal): #Ror
        # could interleave
        yield from right(subst, db, goal.arg(0))
        yield from right(subst, db, goal.arg(1))
    elif smt.is_implies(goal): #Rimpl
        yield from right(subst, avs,ectx, db + [goal.arg(0)], goal.arg(1))
    elif smt.is_quantifier(goal):
        if goal.is_forall(): #Rforall
            vs, body = open_binder(goal)
            avs.extend(vs)
            yield from right(subst, avs, ectx, db, body)
        elif goal.is_exists(): #Rexists
            vs, body = open_binder(goal)
            acpy = avs.copy()
            for v in vs:
                ectx[v] = acpy # allowed universal variables
            yield from right(subst, avs, ectx, db, body)
        else:
            raise Exception("unexpected quantifier in goal", goal)
    elif smt.is_app(goal):
        yield from decide(subst, avs, ectx, db, goal)
    else:
        raise Exception("unexpected goal", goal)

def decide(subst, avs, ectx, db, goal):
    for focus in db:
        yield from left(subst, avs, ectx, db, focus, goal)

def left(subst, ectx, db, focus, goal):
    if smt.is_and(focus):
        for c in focus.children():
            yield from left(subst, ectx, db, c, goal)
    elif smt.is_implies(focus):
        for subst in right(subst, ectx, db, focus.arg(1)):
            yield from left(subst, ectx, db, focus.arg(0), goal)
    elif smt.is_quantifier(focus):
        if focus.is_forall():
            vs, body = open_binder(focus)
            for v in vs:
                ectx[v] = None # can contain anything? sort of distinction of unification variables from db vs goal. Top value in avar lattice
            yield from left(subst, avars, db, body, goal)
        else:
            raise Exception("unexpected quantifier in focus", focus)
    elif smt.is_app(focus):
        # immediately apply subst to... ? Just need a unify that accepts starting subst. Either immiedately apply inb unify or here.
        # substitute(goal, subst); subst1; unify(ectx, focus, goal); yield subst + subst1
        return unify(subst, ectx, focus, goal) # yield from if unify returns multiple results
    else:
        raise Exception("unexpected focus", focus)


def query(db, vs, goal):
    yield from right({}, [], {v:[] for v in vs}, db, goal)
# instead of carrying subst, we could immiedatiely use it.
# big loop isn't great because we don't have a single subst 

# "occurs check" is ||= typing relation
# sigma is ectx
# diswllowed is avars - ectx


```

```python
# applpy ins in focussed mode. We break down d and return al istg of remaining judgements
def apply(d, g):
    vs = []
    #ctx = []
    goals = []
    while True:
        subst = unify(vs,d,g)
        if subst is not None:
            return subst, goals
        elif is_forall(d):
            vs1, d = open_binder(d)
            vs.extend(vs1)
        elif is_implies(d):
            goals.append(d.arg(0))
            d = d.arg(1)
        else:
            return None





```

The Exists formulation of unification is R rules on *goal*.

Forall matching is backchaing after decided.

```python
def z3_match(
    t: smt.ExprRef, pat: smt.ExprRef
) -> Optional[dict[smt.ExprRef, smt.ExprRef]]:
    vs = []
    subst = {}
    todo = [(t, pat)]
    while len(todo) > 0:
        t, pat = todo.pop()
        if t.eq(pat):
            continue
        if smt.is_quantifier(pat) and pat.is_forall():
            vs1, pat = open_binder(pat)
            vs.extend(vs1)
            todo.append((t, pat))
            continue
        if pat in vs:
            if pat in subst:
                if not subst[pat].eq(t):
                    return None
            else:
                subst[pat] = t
            continue
        elif smt.is_app(t) and smt.is_app(pat):
            if pat.decl() == t.decl():
                todo.extend(zip(t.children(), pat.children()))
            else:
                return None
        else:
            raise Exception("Unexpected subterm or subpattern", t, pat)
    return subst

# fill them in, reduce both. Matching modulo R.
def bottom_match(vs, t, pat):
    sterms = set(subterms(t))
    for ts in itertools.product(*[[s for s in sterms if s.sort().eq(v.sort()) ] for v in vs]): # but filtered by type
        t1 = substitute(pat,*zip(vs,ts))
        #if t1.eq(t): # single term match
        #    return dict(zip(vs,ts))
        if t1 in sterms: # all subterms match
            yield zip(vs,ts), t1



```

```python

type searchstate = tuple[Literal["choice", list[searchstate]]]



```

```python
from kdrag.all import *

from typing import NamedTuple
# each of these are _judgments_
# a state of leaves of a proof tree.

class Focused(NamedTuple):
    focus : smt.ExprRef
    goal: smt.BoolRef
    subst: dict[smt.ExprRef, smt.ExprRef]
    ctx: list[smt.BoolRef]

class Unfocused():
    goal: 


type Judgement = Focused | Unfocused

type ProofLeaves = list[Judgement]

class PartialProof(NamedTuple):
    judgements : list[Judgement]
    subst : dict[]


def harrop():
    partial_proofs : list[ProofLeaves] = [[ Unfocused({}, rules, goal) ]]
    while partial_proofs:
        leaves = partial_proofs.pop()
        j = judgements.pop()
        match j:
            case Focused():
            
            case Unfocused(subst, rules, goal):
                if is_and(goal):
                    for g in goal.children():
                        judgements.append( Unfocused(subst, rules, g))
                elif is_or(goal):
                    for g in goal.children():
                        partial_proofs.append(subst, judgements + [Unfocused(subst, rules, g)])
                elif is_implies(goal):







def backchain(ctx, goal):
    if smt.is_and(goal):
        for g in goal.children():
            backchain(ctx, g)
    elif smt.is_or(goal):


    goalstack = [( db, subst,[goal])] # goal stack is kind of a DNF
    while goalstack:
        goals = goalstack.pop()
        while goals:
            goal = goals.pop()
            # right rules
            if smt.is_and(goal):
                goals.extend(goal.children())
            elif smt.is_or(goal):
                for g in goal.children():
                    goalstack.append(goals + [g])
            elif smt.is_implies(goal):
                db.append(goal.arg(0))
                goals.append(goal.arg(1))
            else:
                # decide / select
                for d in db:




def backchain(ctx, goal):
    if smt.is_and(goal):
        for g in goal.children():
            backchain(ctx, g)
    elif smt.is_or(goal):
        for g in goal.children():
            backchain(ctx, g)
    elif smt.is_implies(goal):
        backchain(ctx, goal.children()[1])
    else:
        print(goal)
        print(ctx.check(goal))
        print(ctx.model())
        print()



def left(ctx, d, goal):
    if smt.is_and(goal):
        for g in goal.children():
            left(ctx, d, g)
    elif smt.is_or(goal):
        for g in goal.children():
            left(ctx, d, g)
    elif smt.is_implies(goal):
        left(ctx, d, goal.children()[0])
    else:
        print(goal)
        print(ctx.check(smt.And(d, goal)))
        print(ctx.model())
        print()


```

    Admitting lemma ForAll([x, y, z], mul(x, mul(y, z)) == mul(mul(x, y), z))


    Admitting lemma ForAll(x, Implies(x >= 0, sqrt(x) >= 0))
    Admitting lemma ForAll(x, Implies(x >= 0, sqrt(x)**2 == x))
    Admitting lemma ForAll(x, Implies(x >= 0, sqrt(sqr(x)) == x))
