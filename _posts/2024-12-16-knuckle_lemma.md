---
title: "'Lean-style' Tactics in Knuckledragger"
date: 2024-12-16
---

I've continued tinkering with Knuckledragger, my Z3 powered python proof assistant.

Knuckledragger is an [LCF style](https://www.cl.cam.ac.uk/~jrh13/slides/manchester-12sep01/slides.pdf) proof system in that it distinguishes between a `Proof` and `BoolExpr` datatype and the way to build `Proof` datatypes ultimately only occurs inside a smaller trusted kernel. It is easy if you don't think about such things to kind of conflate a theorem with its formula, since they may look kind of the same in a textbook and a theorem has an associated formula. A theorem can be thought of as it's proof tree so it actually has quite a bit more structure than just the formula.

It is also a [Hilbert style](https://en.wikipedia.org/wiki/Hilbert_system) calculus in the sense that it is a fairly powerful single inference rule with orbiting axioms schemas. The distinction between an axiom schema and an inference rule isn't really that big. An inference rule is something like a function of signature `[Proof] -> Proof` whereas a schema is a theorem parametrized on some non-proof data, for example `[BoolExpr] -> Proof` or `Nat -> Proof`. This is not the only possible computery manifestation of these concepts. For example, in principle an axiom schema could be a generator of `Proof`, although not being able to request the one you want would be extremely inefficient.

An emergent design decision has been to base everything around the Z3py AST and it's bindings. It has worked pretty well. The logic z3 implements is fairly uncontroversial and the bindings are very feature rich and good, even when you aren't using the SMT capabilities persay.

Maybe Knuckledragger is more interesting to some as just a python logical toolkit for the z3 ast. You don't have to use these fun things for ITP. I'm quite excited to build some slow resolution, superposition, tableau, etc ATPs on the Z3 AST using these bits.

Since my last big [summary](https://www.philipzucker.com/state_o_knuck/), I've

- Thrown in [util](https://github.com/philzook58/knuckledragger/blob/main/kdrag/utils.py) algorithms from recent posts. [Pattern unification](https://www.philipzucker.com/ho_unify/), [term orderings](https://github.com/philzook58/knuckledragger/blob/797aae64eeb1e02267505d24a329594c0324a3d1/kdrag/utils.py#L460), a simple [rewriter](https://github.com/philzook58/knuckledragger/blob/d80b1e90c7b00635102c639b46e393f2588e0c8a/kdrag/utils.py#L184) for user rules
- Improved on vampire/eprover support. If vampire has python bindings as good as z3's, it would probably be the superior option as the main solver for Knuckledragger, since ITP often needs a lot of quantifier reasoning. But alas. The impedance mismatch of z3 vs vampire features around lambdas has been a source of pain.
- Tossed in [aprove](https://github.com/philzook58/knuckledragger/blob/main/kdrag/solvers/aprove.py), a termination checker. Not sure what I'm gonna do with this one. Currently knuckledragger offers nothing in regards to checking termination of your recursive definitions
- Tossed in [gappa](https://github.com/philzook58/knuckledragger/blob/main/kdrag/solvers/gappa.py) <https://gappa.gitlabpages.inria.fr/gappa/index.html> which is a system for rigorous floating point bounds
- Tossed in some [sympy](https://github.com/philzook58/knuckledragger/blob/main/kdrag/theories/real/sympy.py) and flint translators. I do not currently trust sympy's results. I'm willing to trust flint as an axiom schema.
- Tossed in some [real](https://github.com/philzook58/knuckledragger/blob/main/kdrag/theories/real/__init__.py) axioms. I don't feel that bad about just axiomatizing them. I mean come on. `sin(0) = 0`. Don't be an ass. Having said that, I wouldn't be surprised if I got a couple wrong. <https://arxiv.org/pdf/0708.3721> This is an interesting paper stating some rigourous upper and lower approximations of common transcendental functions I saw in the [Metitarski](https://www.cl.cam.ac.uk/~lp15/papers/Arith/) paper.
- I added a dumb [Julia](https://julialang.org/) wrapper I haven't done much with yet. <https://github.com/philzook58/Knuckledragger.jl> Could be nice to explore multiple dispatch, nicer syntax and macros that Julia offers. Other interesting high performance stuff.
- Levent Erkok added a knuckledragger like feature to Haskell's SBV <https://hackage.haskell.org/package/sbv-11.0/docs/Data-SBV-Tools-KnuckleDragger.html> I am very happy that these ideas are landing somewhere.
- Tossing in the start of some lark parsers for prolog, tptp, etc

One of the latest additions was actually building a bit of a tactic system that feels akin to lean's, coq's, isabelle's, etc. One thing I really like is that it is just python. If you want to metaprogram, use loops and `try`. Sequencing is python sequencing. The slight cost, like almost all embedded dsls, is that python syntax won't be quite as clean. I think it's pretty good though.

# Tactics

"The purpose of computing is insight, not numbers." - [Richard Hamming](https://en.wikipedia.org/wiki/Richard_Hamming)

I've resisted for a while building a tactic system that looks like Lean, Isabelle's or Coq's, since I kind of wanted to explore this wacky super Hilbert system. I'd hoped (foolishly perhaps), that careful logical manipulation would be unnecessary and that just giving the highlights with the solver filling in the gaps would work. This isn't the right perspective. Even _if_ the solvers were perfect, you aren't. Sometimes I give the solvers the wrong theorem to prove, or the wrong lemmas to do it with. I saw some lectures (podcast?) by Larry Paulson where he made a similar point. Also, the purpose of interactive theorem proving and for that matter a majority of scientific and mathematical computing is _understanding_, not the result itself (businesses would disagree).

# Usage examples

You put the theorem to be proved into `Lemma`. Then you can call a sequence of methods on the `Lemma` object that mutate its proof state.

Most of these examples are automatically discharged by z3 anyway without giving an explicit proof.

```python
from kdrag.all import *
import pprint
p, q, r = smt.Bools("p q r")
pf = kd.lemma(kd.QForAll([p, q], p, smt.Implies(q, p))) # z3 can discharge this one on it's own, don't worry.
l = kd.tactics.Lemma(kd.QForAll([p, q], p, smt.Implies(q, p)))
p1, q1 = l.intros() # open forall binder
body = [l.intros(), # intro p into context
        l.intros(), # intro q into context
        l.assumption()  # use exact p from context
        ]
pprint.pp(body)
l.qed() # returns the actual `Proof` object
```

    [[p!1211] ?|- Implies(q!1212, p!1211),
     [p!1211, q!1212] ?|- p!1211,
     'Nothing to do. Hooray!']

&#8870;ForAll([p, q], Implies(p, Implies(q, p)))

You can see I tried to mimic how the basic tactics look in lean <https://leanprover.github.io/theorem_proving_in_lean4/tactics.html>

The lemma calls return `GoalCtx` objects so that you can see what the system wants at each point interactively in Jupyter.

You can also record these for blog posts which is nice. It is annoying to record these things in Coq, lean, etc. There are systems for it ([Alectryon](https://github.com/cpitclaudel/alectryon), isabelle has nice stuff, maybe other lean blogging stuff?) but it isn't super mainstream.

A cute syntax is to put the steps into list parens `[]`. This let's you structure it using python syntax, and record the intermediate states for when I want to show the intermediate goals in a blog post like this. The walrus `:=` also let's you record your introduced variables inline. Max bernstein showed me a similar pythony list trick for embedded compiler DSLs. It's nice. There is no magic there though, and you don't have to do it if you don't want to.

These proofs steps internally record breadcrumbs about the actual knuckledragger kernel proof inside the `Lemma` object, which is discharged when you call `l.qed()`. I believe this is also true in Coq, lean etc that `qed` actually does the non trivial work of actually checking your proof term in those systems.

Here is a slightly different proof by cases. `auto` just discharges the current goal via `z3`

```python
l = kd.tactics.Lemma(kd.QForAll([p, q], p, q, p))
p1, q1 = l.intros() # open forall binder
body = [l.intros(), # intro And(p,q) into context
        l.cases(p1), # case on p = True vs False
        [l.auto()], 
        [l.auto()]
        ]
pprint.pp(body)
l.qed()
```

    [[And(p!786, q!787)] ?|- p!786,
     [And(p!786, q!787), p!786] ?|- p!786,
     [[And(p!786, q!787), Not(p!786)] ?|- p!786],
     ['Nothing to do. Hooray!']]

&#8870;ForAll([p, q], Implies(And(p, q), p))

You can examine the recorded lemmas if you like used in the `qed`. The first is from introducing the fresh variables, and the later two were created by the calls the `auto` in the two cases.

```python
pprint.pp(("recorded lemmas", l.lemmas))
```

    ('recorded lemmas',
     [|- Implies(Implies(And(p!786, q!787), p!786),
            ForAll([p, q], Implies(And(p, q), p))),
      |- Implies(And(And(p!786, q!787), p!786), p!786),
      |- Implies(And(And(p!786, q!787), Not(p!786)), p!786)])

A proof supplying an appropriate existential witness.

```python
x,y,z = smt.Ints("x y z")
l = kd.tactics.Lemma(smt.Exists([x], x**2 == 4 ))
l.exists(smt.IntVal(2))
l.auto()
l.qed()
```

&#8870;Exists(x, x**2 == 4)

This fails as it should.

```python
x,y,z = smt.Ints("x y z")
l = kd.tactics.Lemma(smt.Exists([x], x**2 == 4 ))
l.exists(smt.IntVal(3))
l.auto()
l.qed()
```

    ---------------------------------------------------------------------------

    LemmaError                                Traceback (most recent call last)

    Cell In[21], line 4
          2 l = kd.tactics.Lemma(smt.Exists([x], x**2 == 4 ))
          3 l.exists(smt.IntVal(3))
    ----> 4 l.auto()
          5 l.qed()


    File ~/Documents/python/knuckledragger/kdrag/tactics.py:260, in Lemma.auto(self)
        258 def auto(self):
        259     ctx, goal = self.goals[-1]
    --> 260     self.lemmas.append(lemma(smt.Implies(smt.And(ctx), goal)))
        261     self.goals.pop()
        262     return self.top_goal()


    File ~/Documents/python/knuckledragger/kdrag/tactics.py:179, in lemma(thm, by, admit, timeout, dump, solver, defns, simps)
        177     if res == smt.sat:
        178         raise kd.kernel.LemmaError(thm, by, "Countermodel", s.model())
    --> 179     raise kd.kernel.LemmaError("lemma", thm, by, res)
        180 else:
        181     core = s.unsat_core()


    LemmaError: ('lemma', Implies(And, 3**2 == 4), [], unknown)

Applying a lemma. `apply` does pattern matching of the goal against the head of the `Proof` you supply.

```python
x,y,z = smt.Ints("x y z")
P = smt.Function("P", smt.IntSort(), smt.BoolSort())
myax : kd.Proof = kd.axiom(smt.ForAll([z], P(z)))
l = kd.tactics.Lemma(kd.QForAll([x], P(x)))
x1 = l.intros()
l.apply(myax)

l.qed()
```

&#8870;ForAll(x, P(x))

This one z3 can't automatically discharge in totality for some reason.

```python
from kdrag.all import *
x,y = smt.Ints("x y")
even = kd.define("even", [x], smt.Exists([y], x == 2 * y))
kd.lemma(kd.QForAll([x], even(x), even(x+2)), by=[even.defn]) # The more raw lowercase lemma tactic.
```

    ---------------------------------------------------------------------------

    LemmaError                                Traceback (most recent call last)

    Cell In[31], line 5
          3 even = kd.define("even", [x], smt.Exists([y], x == 2 * y))
          4 odd = kd.define("odd", [x], smt.Exists([y], x == 2 * y + 1))
    ----> 5 kd.lemma(kd.QForAll([x], even(x), even(x+2)), by=[even.defn]) # The more raw tactic.


    File ~/Documents/python/knuckledragger/kdrag/tactics.py:179, in lemma(thm, by, admit, timeout, dump, solver, defns, simps)
        177     if res == smt.sat:
        178         raise kd.kernel.LemmaError(thm, by, "Countermodel", s.model())
    --> 179     raise kd.kernel.LemmaError("lemma", thm, by, res)
        180 else:
        181     core = s.unsat_core()


    LemmaError: ('lemma', ForAll(x, Implies(even(x), even(x + 2))), [|- ForAll(x, (Exists(y, x == 2*y)) == even(x))], unknown)

But we can get it through using `Lemma` to help it along and give it the proof witness.

```python
l = kd.Lemma(kd.QForAll([x], even(x), even(x+2)))
steps = [
    x1 := l.intros(),
    l.intros(),
    l.apply(even.defn, rev=True),
    l.rewrite(even.defn, at=0, rev=True),
    y1 := l.einstan(0),
    l.exists(y1 + 1),
    l.auto(),
]
pprint.pp(steps)
l.qed()
```

    [x!1169,
     [even(x!1169)] ?|- even(x!1169 + 2),
     [even(x!1169)] ?|- Exists(y, x!1169 + 2 == 2*y),
     [Exists(y, x!1169 == 2*y)] ?|- Exists(y, x!1169 + 2 == 2*y),
     y!1172,
     [x!1169 == 2*y!1172] ?|- x!1169 + 2 == 2*(y!1172 + 1),
     'Nothing to do. Hooray!']

&#8870;ForAll(x, Implies(even(x), even(x + 2)))

# How it works

To be perfectly honest, aspects of the design are pure cargo culting.

The `Lemma` object holds a goal stack and the different tactics push on and pop off different amounts of goals off the stack.

The currently needed goal is represented as a named tuple.

```python
from kdrag.all import *
from typing import NamedTuple
class GoalCtx(NamedTuple):
    ctx: list[smt.BoolRef]
    goal: smt.BoolRef

    def __repr__(self):
        return repr(self.ctx) + " ?|- " + repr(self.goal)

```

When you make a Lemma object, it starts with the theorem to be proved as a goal in an empty context.

When an actual `Proof` is made by a call to the kernel, it is recorded in `self.lemmas`. This is a somewhat lazy design, hoping z3 is powerful enough to assemble all the steps later. It may not be, as I have found sometimes z3 to not push through very trivial single step stuff involving quantifiers. We'll see.

When you see a forall quantifier, you can fix it. I added new axiom schema to the kernel that create fresh variables. This is one of a couple ways to emulate the ability of having fresh constants in my Hilbert style rpoof system

```python
# in Kernel
def herb(thm: smt.QuantifierRef) -> tuple[list[smt.ExprRef], Proof]:
    """
    Herbrandize a theorem.
    It is sufficient to prove a theorem for fresh consts to prove a universal.
    Note: Perhaps lambdaized form is better? Return vars and lamda that could receive `|- P[vars]`
    """
    assert smt.is_quantifier(thm) and thm.is_forall()
    herbs = fresh_const(thm)
    return herbs, __Proof(
        smt.Implies(smt.substitute_vars(thm.body(), *reversed(herbs)), thm),
        reason="herband",
    )
```

There are also new axiom schema in the kernel for existential manipulation. Names may change. `forget2` is existential introduction using some particular terms `ts` and `einstan` is existential instantiation with a fresh constant. These are the two basic rules for manipulating existential quantifiers.

```python
def forget2(ts: list[smt.ExprRef], thm: smt.QuantifierRef) -> Proof:
    """
    "Forget" a term using existentials. This is existential introduction.
    `P(ts) -> exists xs, P(xs)`
    `thm` is an existential formula, and `ts` are terms to substitute those variables with.
    forget easily follows.
    https://en.wikipedia.org/wiki/Existential_generalization
    """
    assert smt.is_quantifier(thm) and thm.is_exists() and len(ts) == thm.num_vars()
    return __Proof(
        smt.Implies(smt.substitute_vars(thm.body(), *reversed(ts)), thm),
        reason="exists_intro",
    )


def einstan(thm: smt.QuantifierRef) -> tuple[list[smt.ExprRef], Proof]:
    """
    Skolemize an existential quantifier.
    `exists xs, P(xs) -> P(cs)` for fresh cs
    https://en.wikipedia.org/wiki/Existential_instantiation
    """
    # TODO: Hmm. Maybe we don't need to have a Proof? Lessen this to thm.
    assert smt.is_quantifier(thm) and thm.is_exists()

    skolems = fresh_const(thm)
    return skolems, __Proof(
        smt.Implies(thm, smt.substitute_vars(thm.body(), *reversed(skolems))),
        reason=["einstan"],
    )
```

Note that `qed` just dumps all the `self.lemmas` into a call to `kernel.lemma` where z3 tries to assemble the whole thing.

This is the current source of the `Lemma` object <https://github.com/philzook58/knuckledragger/blob/d80b1e90c7b00635102c639b46e393f2588e0c8a/kdrag/tactics.py#L209> .  This will all probably continue to evolve.

```python
class Lemma:
    def __init__(self, goal: smt.BoolRef):
        self.lemmas = []
        self.thm = goal
        self.goals = [GoalCtx([], goal)]

    def fixes(self):
        ctx, goal = self.goals[-1]
        if smt.is_quantifier(goal) and goal.is_forall():
            self.goals.pop()
            vs, herb_lemma = kd.kernel.herb(goal)
            self.lemmas.append(herb_lemma)
            self.goals.append(GoalCtx(ctx, herb_lemma.thm.arg(0)))
            return vs
        else:
            raise ValueError(f"fixes tactic failed. Not a forall {goal}")

    def intros(self):
        ctx, goal = self.goals.pop()
        if smt.is_quantifier(goal) and goal.is_forall():
            vs, herb_lemma = kd.kernel.herb(goal)
            self.lemmas.append(herb_lemma)
            self.goals.append(GoalCtx(ctx, herb_lemma.thm.arg(0)))
            if len(vs) == 1:
                return vs[0]
            else:
                return vs
        elif smt.is_implies(goal):
            self.goals.append(GoalCtx(ctx + [goal.arg(0)], goal.arg(1)))
            return self.top_goal()
        elif smt.is_not(goal):
            self.goals.append((ctx + [goal.arg(0)], smt.BoolVal(False)))
            return
        else:
            raise ValueError("Intros failed.")

    def cases(self, t):
        ctx, goal = self.goals.pop()
        if t.sort() == smt.BoolSort():
            self.goals.append(GoalCtx(ctx + [smt.Not(t)], goal))
            self.goals.append(GoalCtx(ctx + [t], goal))
        elif isinstance(t, smt.DatatypeRef):
            dsort = t.sort()
            for i in reversed(range(dsort.num_constructors())):
                self.goals.append(GoalCtx(ctx + [dsort.recognizer(i)(t)], goal))
        else:
            raise ValueError("Cases failed. Not a bool or datatype")
        return self.top_goal()

    def auto(self):
        ctx, goal = self.goals[-1]
        self.lemmas.append(lemma(smt.Implies(smt.And(ctx), goal)))
        self.goals.pop()
        return self.top_goal()

    def einstan(self, n):
        ctx, goal = self.goals[-1]
        formula = ctx[n]
        if smt.is_quantifier(formula) and formula.is_exists():
            self.goals.pop()
            fs, einstan_lemma = kd.kernel.einstan(formula)
            self.lemmas.append(einstan_lemma)
            self.goals.append(
                GoalCtx(ctx[:n] + [einstan_lemma.thm.arg(1)] + ctx[n + 1 :], goal)
            )
            if len(fs) == 1:
                return fs[0]
            else:
                return fs
        else:
            raise ValueError("Einstan failed. Not an exists")

    def split(self, at=None):
        ctx, goal = self.goals[-1]
        if at is None:
            if smt.is_and(goal):
                self.goals.pop()
                self.goals.extend([GoalCtx(ctx, c) for c in goal.children()])
            if smt.is_eq(goal):
                self.goals.pop()
                self.goals.append(GoalCtx(ctx, smt.Implies(goal.arg(0), goal.arg(1))))
                self.goals.append(GoalCtx(ctx, smt.Implies(goal.arg(1), goal.arg(0))))
            else:
                raise ValueError("Split failed")
        else:
            if smt.is_or(ctx[at]):
                self.goals.pop()
                for c in ctx[at].children():
                    self.goals.append(GoalCtx(ctx[:at] + [c] + ctx[at + 1 :], goal))
            if smt.is_and(ctx[at]):
                self.goals.pop()
                self.goals.append(
                    GoalCtx(ctx[:at] + ctx[at].children() + ctx[at + 1 :], goal)
                )
            else:
                raise ValueError("Split failed")

    def left(self, n=0):
        ctx, goal = self.goals[-1]
        if smt.is_or(goal):
            if n is None:
                n = 0
            self.goals[-1] = GoalCtx(ctx, goal.arg(n))
            return self.top_goal()
        else:
            raise ValueError("Left failed. Not an or")

    def right(self):
        ctx, goal = self.goals[-1]
        if smt.is_or(goal):
            self.goals[-1] = GoalCtx(ctx, goal.arg(goal.num_args() - 1))
            return self.top_goal()
        else:
            raise ValueError("Right failed. Not an or")

    def exists(self, *ts):
        ctx, goal = self.goals[-1]
        lemma = kd.kernel.forget2(ts, goal)
        self.lemmas.append(lemma)
        self.goals[-1] = GoalCtx(ctx, lemma.thm.arg(0))
        return self.top_goal()

    def rewrite(self, rule, at=None, rev=False):
        """
        `rewrite` allows you to apply rewrite rule (which may either be a Proof or an index into the context) to the goal or to the context.
        """
        ctx, goal = self.goals[-1]
        if isinstance(rule, int):
            rulethm = ctx[rule]
        elif kd.kernel.is_proof(rule):
            rulethm = rule.thm
        if smt.is_quantifier(rulethm) and rulethm.is_forall():
            vs, body = kd.utils.open_binder(rulethm)
        else:
            vs = []
            body = rulethm
        if smt.is_eq(body):
            lhs, rhs = body.arg(0), body.arg(1)
            if rev:
                lhs, rhs = rhs, lhs
        else:
            raise ValueError(f"Rewrite tactic failed. Not an equality {rulethm}")
        if at is None:
            target = goal
        elif isinstance(at, int):
            target = ctx[at]
        else:
            raise ValueError(
                "Rewrite tactic failed. `at` is not an index into the context"
            )
        subst = kd.utils.pmatch_rec(vs, lhs, target)
        if subst is None:
            raise ValueError(
                f"Rewrite tactic failed to apply lemma {rulethm} to goal {goal}"
            )
        else:
            self.goals.pop()
            lhs1 = smt.substitute(lhs, *[(v, t) for v, t in subst.items()])
            rhs1 = smt.substitute(rhs, *[(v, t) for v, t in subst.items()])
            target: smt.BoolRef = smt.substitute(target, (lhs1, rhs1))
            self.lemmas.append(kd.kernel.instan2([subst[v] for v in vs], rulethm))
            if kd.kernel.is_proof(rule):
                self.lemmas.append(rule)
            if at is None:
                self.goals.append(GoalCtx(ctx, target))
            else:
                self.goals.append(GoalCtx(ctx[:at] + [target] + ctx[at + 1 :], goal))
            return self.top_goal()

    def rw(self, rule, at=None, rev=False):
        return self.rewrite(rule, at=at, rev=rev)

    def unfold(self, decl: smt.FuncDeclRef):
        if hasattr(decl, "defn"):
            return self.rewrite(decl.defn)
        else:
            raise ValueError("Unfold failed. Not a defined function")

    def apply(self, pf: kd.kernel.Proof, rev=False):
        ctx, goal = self.goals.pop()
        thm = pf.thm
        if smt.is_quantifier(thm) and thm.is_forall():
            vs, thm = kd.utils.open_binder(thm)
        else:
            vs = []
        if smt.is_implies(thm):
            pat = thm.arg(1)
        elif smt.is_eq(thm):
            if rev:
                pat = thm.arg(1)
            else:
                pat = thm.arg(0)
        else:
            pat = thm
        subst = kd.utils.pmatch(vs, pat, goal)
        if subst is None:
            raise ValueError(f"Apply tactic failed to apply lemma {pf} to goal {goal} ")
        else:
            pf1 = kd.kernel.instan([subst[v] for v in vs], pf)
            self.lemmas.append(pf1)
            if smt.is_implies(pf1.thm):
                self.goals.append(GoalCtx(ctx, pf1.thm.arg(0)))
            elif smt.is_eq(pf1.thm):
                if rev:
                    self.goals.append(GoalCtx(ctx, pf1.thm.arg(0)))
                else:
                    self.goals.append(GoalCtx(ctx, pf1.thm.arg(1)))
        return self.top_goal()

    def assumption(self):
        ctx, goal = self.goals.pop()
        if any([goal.eq(h) for h in ctx]):
            return self.top_goal()
        else:
            raise ValueError("Assumption tactic failed", goal, ctx)

    def have(self, conc, **kwargs):
        ctx, goal = self.goals.pop()
        self.lemmas.append(lemma(smt.Implies(smt.And(ctx), conc)), **kwargs)
        self.goals.append(GoalCtx(ctx + [conc], conc))
        return self.top_goal()

    # TODO
    # def search():
    # def calc

    def top_goal(self):
        if len(self.goals) == 0:
            return "Nothing to do. Hooray!"
        return self.goals[-1]

    def __repr__(self):
        return repr(self.top_goal())

    def qed(self):
        return kd.kernel.lemma(self.thm, by=self.lemmas)
```

# Bits and Bobbles

Calling them "lean"-style in the post is ridiculous, because this ctyle of tactic precedes lean by a lot. But I did model my particular choice of tactic names after lean's, so whatever. Makes for a punchier title.

<https://www.philipzucker.com/programming-and-interactive-proving-with-z3py/> I wrote a similar set of ideas 5 years ago (yikes). The main difference here is that I didn't have the idea of using the logical kernel of Knuckledragger. Maybe in some respects what I did here is better or simpler.

I hope that these lemma breadcrumbs are sufficient for the final `qed` lemma to finish. There is not guarantee of it, and this failure would be quite frustrating.

It was useful to peek on the goalstack and the pop only once I know it will succeed. Then the `Lemma` object isn't mutated until the tactium is successful.

It may bite me in the ass someday that Lemma is imperative. It does perhaps stop some kinds of proof search. Not sure. It was the easiest thing to do so YOLO.

I should be recording the fresh constants in the GoalCtx.

I haven't bolted in induction yet. It might not be that bad. I do have induction schema.

I might need new axioms to perform generalization. That the multi arity quantifiers are one-shot might be a problem.

A general blog post on translation of natural deduction to hilbert style systems could be interesting. In a sense, this is what my tactic is doing, albiet in an unprincipled way. When Hilbert stykle was established but before nat deduct was taken for granted, this was probably fairly crucial

A tactics system manipulates partial proofs.

What the hell are partial proofs? Good question.

A tactics system can be implemented in a fairly imperative way.

There are backwards tactics that manipulate the goal and forward tactics that manipulate the context.

tactics have something to do with lenses. You move backwards, breaking apat the goal, but then there is a forward "thing" that builds the actual proof object and remembers pieces. Food for thought.

Non terminating definitions aren't necessarily unsound or even implying new nonstandard elements of you domain. The classic mistake of `fact(x) = if x == 0 then 1 else x * fact(x - 1)` rather than something like `fact(x) = if x <= 0 then 1 else x * fact(x-1)` is a fine "definition" of `fact(x) == 0 if x < 0`. Depends what you mean by definition maybe.

### Backwards

Many backwards tactics correspond to the rules of [natural deduction](https://plato.stanford.edu/entries/natural-deduction/) read from below to inference line moving up.

| Lean   | Nat Deduct  |
|----|---|
| intros | forall/impl introduction |
| apply | impl elim |
| exists | exist intro |
| left/right | or intro |
| constructor | and intro |

<https://people.mpi-sws.org/~skilpat/plerg/papers/open-proofs-2up.pdf>  Open Proofs and Open Terms: a Basis for
Interactive Logic <https://dl.acm.org/doi/10.5555/647852.737415>  Herman Geuvers, Gueorgui I. Jojgov

<https://arxiv.org/pdf/1703.05215>  Algebraic Foundations of Proof Refinement - Sterling Harper

<https://leanprover-community.github.io/logic_and_proof/propositional_logic_in_lean.html>

<https://leanprover.github.io/theorem_proving_in_lean4/tactics.html>

Emergently, knuckledragger is looking like a python port of some aspects of Why3. One big difference is I have not made a new IR separated from smtlib.

Good discussion of LCF in Harrison's handbook of practical logic and automated reasoning.
<https://lawrencecpaulson.github.io/2022/01/05/LCF.html>

Prove some of those lemmas follow each other

The modulus vs non modulus version.

```python
from kdrag.all import *
IntList = smt.Datatype("IntList")
IntList.declare("nil")
IntList.declare("cons", ("car", smt.IntSort()), ("cdr", IntList))
IntList = IntList.create()

x = smt.Const("x", IntList)
length = smt.Function("length", IntList, smt.IntSort())
length = kd.define("length", [x], smt.If(x.is_nil, 0, 1 + length(x.cdr)))

# fails
#kd.kernel.lemma(kd.QForAll([x], length(x) >= 0), by=[length.defn])
l = kd.Lemma(smt.ForAll([x], length(x) >= 0))
#x1 = l.intros()
import kdrag.theories.datatypes as dt
intinduct = dt.induct(IntList)
#l.apply(intinduct)
l.apply(intinduct) # So. Forall x, (stuff), P(x)) vs stuff => forall x, P(x).
l.split()
[
    a := l.intros(),
    l.intros(),
    l.z3simp(),
    hd := l.intros(),
    l.unfold(length),
    l.auto() # auto(by=[length.defn])
]
[
    l.z3simp(),
    l.unfold(length),
    l.auto()
]
l.qed()
```

&#8870;ForAll(x, length(x) >= 0)

```python
from kdrag.all import *

p,q,r = smt.Bools("p q r")
l = kd.tactics.Lemma2(smt.Implies(p,p))

l.qed()


```

&#8870;Implies(p, p)

```python
from kdrag.all import *

p,q,r = smt.Bools("p q r")
l = kd.tactics.Lemma2(kd.QForAll([p,q],p,q,p))
p1,q1 = l.intros()
l.intros()
l.cases(p1)
l.auto()
l.auto()
#l.auto()
#l.qed()

```

    Nothing to do. Hooray!

```python
from kdrag.all import *
x,y,z = smt.Ints("x y z")
l = kd.tactics.Lemma2(smt.Exists([x], x**2 == 4 ))
l.exists(smt.IntVal(2))
l.auto()
l.qed()


l = kd.tactics.Lemma2(smt.Exists([x, y], smt.And(x == 2, y == 3)))
l.exists(smt.IntVal(2), smt.IntVal(3))
l.auto()

#l.qed()
l.lemmas
```

    [|- Implies(And(2 == 2, 3 == 3),
             Exists([x, y], And(x == 2, y == 3))),
     |- Implies(And, And(2 == 2, 3 == 3))]

```python
from kdrag.all import *
x,y,z = smt.Ints("x y z")
P = smt.Function("P", smt.IntSort(), smt.BoolSort())
myax = kd.axiom(smt.ForAll([z], P(z)))
l = kd.tactics.Lemma(kd.QForAll([x], P(x)))
x1 = l.intros()
l.apply(myax)

l.qed()

```

    P(Z!210) True [Z!210]
    pmatch [] P(Z!210) P(x!209) {}
    pmatch [] Z!210 x!209 {}

&#8870;ForAll(x, P(x))

This is the first time I recall seeing z3 swap the order of what I gave it...
Is it the exists that is doing this?

```python
#smt.ForAll([x], even(x) == (x == 2 * y))
import z3
x,y = z3.Ints("x y")
(x >= 14) == z3.Exists([y], x == 2 * y) # swaps order of eqaution
(x >= 14) == z3.ForAll([y], x == 2 * y) # swaps order of equation
z3.ForAll([x], (x >= 14)) == z3.Exists([y], x == 2 * y) # doesn't swap
f = z3.Const("f", z3.ArraySort(z3.IntSort(), z3.BoolSort()))
f == z3.Lambda([x], x == 2 * y) #doesn't swap
z3.Exists([y], x == 2 * y) == (x >= 14) # doesn't swap
```

(&exist;y : x = 2&middot;y) = (x &ge; 14)

```python
(z3.IntVal(13) >= z3.IntVal(1) + z3.IntVal(2)) == z3.Exists([y], x == 2 * y)
```

(&exist;y : x = 2&middot;y) = (13 &ge; 1 + 2)

```python
z3.IntVal(1) + z3.IntVal(2) == z3.IntVal(3)
```

3 = 1 + 2

```python
z3.get_version_string()
```

    '4.13.3'

```python
z3.IntVal(1) + z3.IntVal(2) == z3.IntVal(3)
z3.IntVal(3) == z3.IntVal(1) + z3.IntVal(2) 
z3.IntVal(2) + z3.IntVal(5)  == z3.IntVal(1) + z3.IntVal(2) 
```

2 + 5 = 1 + 2

```python
from kdrag.all import *
x,y = smt.Ints("x y")
even = kd.define("even", [x], smt.Exists([y], x == 2 * y))
odd = kd.define("odd", [x], smt.Exists([y], x == 2 * y + 1))


for i in range(100):
    evdef2 = kd.lemma(smt.ForAll([x], even(x) == smt.Exists([y], x == 2 * y)), by=[even.defn])
    l = kd.Lemma(kd.QForAll([x], even(x), even(x+2)))
    x1 = l.intros()
    l.intros()
    l.apply(even.defn, rev=True)
    l.rewrite(even.defn, at=0, rev=True)
    y1 = l.einstan(0)
    l.exists(y1 + 1)
    l.auto()
    l.qed()
    #kd.kernel.lemma(kd.QForAll([x], even(x), even(x+2)), by=[even.defn])
    #l.exists(y1 + 1)
    #evdef2.thm.body()

    l = kd.Lemma(kd.QForAll([x], even(x), even(x+2)))
    [
        x1 := l.intros(),
        l.intros(),
        l.apply(even.defn, rev=True),
        l.rewrite(even.defn, at=0, rev=True),
        y1 := l.einstan(0),
        l.exists(y1 + 1),
        l.auto(),
    ]
    l.qed()


```

```python
from kdrag.all import *

IntList = smt.Datatype("IntList")
IntList.declare("nil")
IntList.declare("cons", ("car", smt.IntSort()), ("cdr", IntList))
IntList = IntList.create()

x, y = smt.Consts("x y", IntList)
z = smt.Int("z")

l = kd.lemma(
    smt.ForAll(
        [x], smt.Or(x == IntList.nil, smt.Exists([y, z], x == IntList.cons(z, y)))
    )
)
l = kd.Lemma(
    smt.ForAll(
        [x], smt.Or(x == IntList.nil, smt.Exists([z, y], x == IntList.cons(z, y)))
    )
)
[
    x1 := l.intros(),
    l.cases(x1),
    [l.left(), l.auto()],
    [l.right(), l.exists(x1.car, x1.cdr), l.auto()],
]
l.qed()

# kd.kernel.lemma(smt.ForAll([x], smt.Implies(x.is_cons, x == IntList.cons(x.car,x.cdr))))
# l.goals[-1].goal
```

&#8870;ForAll(x, Or(x == nil, Exists([z, y], x == cons(z, y))))

```python
from kdrag.all import *
x = smt.Int("x")
sqr = kd.define("sqr", [x], x * x)
l = kd.Lemma(smt.ForAll([x], sqr(x) == x * x))
l.intros()
l.unfold(sqr)
l.auto()
l.qed()
l = kd.Lemma(smt.ForAll([x], sqr(sqr(x)) == x*x*x * x))
l.intros()
l.unfold(sqr)
l.unfold(sqr)
l.auto()
l.qed()

```

&#8870;ForAll(x, sqr(sqr(x)) == x*x*x*x)

```python
foo = smt.Datatype("foo")
foo.declare("biz", ("myint", smt.IntSort()))
foo = foo.create()
foo.is_biz
```

    'is(biz)'

<https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html>

```python
from kdrag.all import *
m,n = smt.Ints("m n")
l = kd.Lemma(kd.QForAll([m,n], smt.Or(m == 0, n == 0), m*n == 0))
m1,n1 = l.intros()
l.intros()
l.cases(m1 == 0)
l.auto()
l.have(n1 == 0)

```

    [Or(m!588 == 0, n!589 == 0), Not(m!588 == 0), n!589 == 0] ?|- n!589 == 0

```python
l.auto()
l.qed()
kd.lemma(kd.QForAll([m,n], smt.Or(m == 0, n == 0), m*n == 0))
```

```python
from kdrag.all import *
p,q = smt.Bools("p q")
l = kd.Lemma(smt.Implies(p, smt.Or(p,q)))
l.intros()
l.left()
l.auto()
l.qed()

l = kd.Lemma(smt.Implies(q, smt.Or(p,p,p,q,p)))
l.intros()
l.left(3)
l.auto()
l.qed()

l = kd.Lemma(smt.Implies(p, smt.Or(q,q,q,p)))
l.intros()
l.right()
l.qed()

```

&#8870;Implies(p, Or(q, q, q, p))

# sympy tactical

Use sympy to derive new simplification goals.

Maybe try to automatically derive, but if can't just put the equation on the goal stack.

Use singularities as warnings.

```python
def expand(l : Lemma, t:term):
    vs, ctx, goal = l.top_goal()
    newt = smt_of_sympy(sympy_of_smt(vs, t).expand())
    goals.pop()
    goals.append(Sequent(vs,ctx + [t == newt], goals))
    goals.append(Sequent(vs,goals, t == newt)
    try:
        l.auto()
    except:
        pass
def lim(self):
def integ():
def trigexpand():
def trigreduce():
def factor():
def simplify(l):
    
```

```python


```

&#8870;ForAll(x, length(x) >= 0)

I susepct
