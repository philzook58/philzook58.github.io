---
title: Proof Rules for MetaSMT
date: 2025-09-22
---

Knuckledragger <https://github.com/philzook58/knuckledragger> is my system for interactive theorem proving in python. The core system is not python specific and has some interesting theoretical aspects.

It is designed to be a minimal layer on top of the existing successful SMT systems to be metaprogrammed in your programming language of choice.

A sequence of related SMT solves is the core of many automated software verification tools. There is a hand waving of sorts how these (mangled) calls combine into the larger property of interest. It is a natural if one wants a more rigorous approach to work within the language of SMT if possible rather than required a radical switch to a whole new system like Lean or Isabelle.

SMT solvers themselves are interested in producing proof certificates for their internal reasoning, both for self checking and for translation into systems like Lean and Isabelle. <https://cs.stanford.edu/~preiner/publications/2023/BarbosaBCDKLNNOPRTZ-CACM23.pdf> <https://github.com/Z3Prover/z3/discussions/5981> I consider this area well attacked by the people most qualified to attack it, the SMT authors themselves. However, it is outside the solver's purview to check the reasoning _linking_ user calls. This is where the proof rules of knuckledragger come in.

There are other proof systems like F* and Dafny that deeply integrate with SMT solvers from the get go, but the design here is take the logic the SMT solver gives and work with it, warts,  and all. A lot of inexpressivity can be papered over by rich metaprogramming in a host language (python here, but others work). This is the opposite approach to systems that try to internalize as much as possible <https://www.reddit.com/r/ProgrammingLanguages/comments/1aigns2/discussing_isabellehol_a_proof_assistant_for/kova7l5/> . There is a lot to be said to having these richer systems, but I feel the weak logic macro approach is underexplored these days.

SMT solvers can only scale so far at which point a large query may need to be broken up into multiple pieces. An SMT solver will never prove Fermat's Last Theorem given the axioms of set theory in one shot.

In this respect, the proof system of Knuckledragger is a MetaSMT proof system.

I'll note that basically the formulas of SMTLIB is monomorphic higher order logic, so the logic itself is quite well trodden.

# LCF Architecture

Software and programming languages have a variety of protection mechanisms for the sanctity of information, invariants, and data structures. Permissions, cryptographic signing, smart constructors, public and private interfaces. Probably all of these mechanisms can be used in one way or another as the foundation of a proof assistant. <https://www.philipzucker.com/python-itp/>

The LCF approach has a special datatype `Proof` with smart constructors. Inference rules are mapped into trusted functions that take in `Proof`, any auxiliary data and produce new `Proof`. Axiom schema are just a special case of an inference rule that does not require any `Proof` arguments.

Knuckledragger is written using this style. A distinction in some manner between formulas that _are to be proven_ and formulas that _have been proven_ is crucial, and a datatype distinction is a natural way to do so.

The internals of the Proof datatype are irrelevant to the user. At minimum it should store the formula in question that has been proven, but it may also contain a record/trace of the steps/api calls that led to it's production. A sufficiently complete API trace such that it can be replayed is a proof object/tree. Complete API traces are very powerful, for example a trace of all syscalls of a IO reading and writing program are succificent to completely determinize it.

<https://github.com/philzook58/knuckledragger/blob/4ecf328b8e0b31c7330ef53102d2812b96522469/src/kdrag/kernel.py#L30>

See Harrison <https://www.cl.cam.ac.uk/~jrh13/atp/> <https://www.cl.cam.ac.uk/~jrh13/slides/manchester-12sep01/slides.pdf> or Paulson <https://lawrencecpaulson.github.io/2022/01/05/LCF.html> for more.

# Core Proof Rules

## Mega Modus

SMT solvers have a model like character, answering satisfisability (model existence) or unsatisfiability (mode non existence) questions. For this reason the main judgement of knuckeldragger is written using a `|=` instead of a `|-`.

`|=` is informally specified but includes an understanding of which model of the integers, reals, and booleans baked into the SMT solver. Metatheoretically modelling `|=` could be done inside a proof assistant like Lean for example.

SMT solvers are not exactly a random collection of features, although they are also that. The language of SMTLIB and the solvers themselves encode roughly decidable theories via an evolutionary forcing desire to remain fast and reliable.

The degree to which SMT solvers do handle some undecidable queries, they are within their rights to bail out at `unknown` or have a timeout.

For this reason, there is a subset of a large `|=` which can be automatically handled `|=_dec` and `|=_auto`.

```

|= P1   |= P2    ...   {P1,P2,...} |=_auto P
--------------------------------------------
                 |= P
```

<https://github.com/philzook58/knuckledragger/blob/4ecf328b8e0b31c7330ef53102d2812b96522469/src/kdrag/kernel.py#L129>

```python
import kdrag.smt as smt
import kdrag as kd

x,y,z = smt.Ints('x y z')
kd.kernel.prove(smt.ForAll([x], x + 1 > x))
```

&#x22A8;ForAll(x, x + 1 > x)

```python
pfP1 = kd.axiom(x > 0)
pfP2 = kd.axiom(y > 0)
pf = kd.kernel.prove(y + x > 0, by=[pfP1, pfP2])
pf
```

&#x22A8;y + x > 0

```python
pf.reason
```

    [|= x > 0, |= y > 0]

## Definitions

A relatively underemphasized aspect of logic is definitional mechanisms. <https://en.wikipedia.org/wiki/Conservative_extension>
For some reason many mathematical logic textbooks seem to think it is acceptable to have all names and definitions to be basically at the metalevel. This seems kind of nuts.

As a MetaSMT system, this is a crucial aspect, as we expect o build abstractions and then reason about the abstractions without giving the solver access to the original definitions. To some degree, theorem proving is all about defining abstractions and unfolding them only at special points in order to build new pinrciples at which to reason at.

<https://github.com/philzook58/knuckledragger/blob/4ecf328b8e0b31c7330ef53102d2812b96522469/src/kdrag/kernel.py#L232>

Definitions are registered into a dictionary kept in the kernel. Definitions return an axiom of the form `|= forall args, myfun(args) == body` .

It has turned out to be important to make definitions fast and reliable to unfold.

There is also the general logical design principle that any "introduction" of a capability should be pair with an ability to use the capability.

An emergent principle is that any functionality z3 exposes should be wrapped as a proof rule it it makes sense.

Z3 exposes a function `substitute_funs` which can quickly unfold a definitions for a function symbol. This is wrapped by unfoldm which takesin which definitions to unfold as a parameter.

<https://github.com/philzook58/knuckledragger/blob/4ecf328b8e0b31c7330ef53102d2812b96522469/src/kdrag/kernel.py#L309>

```python
myadd = kd.define("myadd", [x,y], x + y)
kd.kernel.defns[myadd]
```

    Defn(name='myadd', args=[x, y], body=x + y, ax=|= ForAll([x, y], myadd(x, y) == x + y), subst_funs_body=Var(0) + Var(1))

```python
kd.kernel.is_defined(myadd(x,y))
```

    True

```python
kd.kernel.unfold(myadd(1,2), [myadd])
```

    (1 + 2, |= myadd(1, 2) == 1 + 2)

Reliable unfold is extremely useful and important. The definitional equality of knuckledragger, to the degree there is a single one, is the iteration of `z3.simplify` and `unfold`. This is available as a tactic at `kd.rewrite.full_simp`

## Quantifiers

Quantifiers are an extremely useful modelling feature. Proofs using them require more invention/synthesis than simple quantifier free reasoning. It certainly helps the solver if you point out which terms to instantiate the quantifier with.

### Universal

`instan` <https://github.com/philzook58/knuckledragger/blob/4ecf328b8e0b31c7330ef53102d2812b96522469/src/kdrag/kernel.py#L354> Takes a proof of the form `|= forall x, P(x)` and can instantiate the vairable with any term `t` to `|= P(t)`.

The design choice of taking the Formula datatypes and semantics of SMTLIB as they are presents an interesting technical challenge. Sometimes constraints guide one to beauty, like the rigid forms of poetry.

Many proof system's term datatype includes a `Var` constructor, standin in for a schematic variable. Any proof derived with a variable in it may be arbitrarily instantiated to get a more concrete proof. This is the setup for example in quantifier free equational logic.

The Z3 AST does not have such a constructor.

The original approach taken by Knuckledragger was to use a herbrandization axiom schema <https://github.com/philzook58/knuckledragger/blob/4ecf328b8e0b31c7330ef53102d2812b96522469/src/kdrag/kernel.py#L442> , which generates a fresh constant and also an axiom that `P[x] => forall y, P[y]`. This schema has the flavor of opening a binder in a proof assistant.

What knuckledragger _does_ have control over is it's judgement forms. `|= P` is a judgement at the knuckledragger layer. There is a refactroing possible between the term data type and the judgement forms. A new judgement `x freshvar` makes it possible to have schematic variables.

```
|= forall x, P(x)     
------------------ instan
      |= P(t)


|= P(x)    x freshvar
------------------------- generalize
      |= forall x, P(x)


   x is freshly generated
--------------------------- FreshVar
    x freshvar
```

```python
x,y,z = kd.FreshVars("x y z", smt.IntSort())
x
```

x!0

```python
kd.kernel.is_fresh_var(x)
```

    True

```python
a = smt.Int("a")
kd.kernel.is_fresh_var(a)
```

    False

```python
pf = kd.prove(x + 1 > x)
pf
```

&#x22A8;x!0 + 1 > x!0

```python
pf2 = kd.kernel.generalize([x], pf)
pf2
```

&#x22A8;ForAll(x!0, x!0 + 1 > x!0)

```python
pf2(smt.IntVal(42))
```

&#x22A8;42 + 1 > 42

```python
kd.kernel.instan([smt.IntVal(42)], pf2)
```

&#x22A8;42 + 1 > 42

```python
kd.kernel.generalize([a], pf) # should fail, since a is not fresh
```

    ---------------------------------------------------------------------------

    AssertionError                            Traceback (most recent call last)

    Cell In[20], line 1
    ----> 1 kd.kernel.generalize([a], pf) # should fail, since a is not fresh


    File ~/Documents/python/knuckledragger/src/kdrag/kernel.py:680, in generalize(vs, pf)
        670 def generalize(vs: list[smt.ExprRef], pf: Proof) -> Proof:
        671     """
        672     Generalize a theorem with respect to a list of schema variables.
        673     This introduces a universal quantifier for schema variables.
       (...)    678     |= ForAll([x!..., y!...], x!... == x!...)
        679     """
    --> 680     assert all(is_fresh_var(v) for v in vs)
        681     assert isinstance(pf, Proof)
        682     return axiom(smt.ForAll(vs, pf.thm), by=["generalize", vs, pf])


    AssertionError: 

### Existential

Existentials have not been as thoroughly tested as the universal quantifiers so pain points may still exist. There are often useful ways to formulate theories without lots of existentials, but it is difficult to avoid universal in interesting theories.

The basic rules are `forget`, `einstan`, and `skolem`.

## Induction

Z3 comes with algebraic datatypes, but does not have built in reasoning for induction over these types.
By traversing the constructors, one can build an induction principle.

These induction principles could be generated as a principle in higher order logic `|= forall P, cases => forall x, P(x)` or instead as an axiom schema `def induct(P,x): return "|= cases => P(x)"`. These two forms are interderivable, but the axiom schema form has been found to be more directly useful in the backwards tactic system.

<https://github.com/philzook58/knuckledragger/blob/4ecf328b8e0b31c7330ef53102d2812b96522469/src/kdrag/kernel.py#L550>

```python
from kdrag.theories.nat import Nat
n = smt.Const("n", Nat)
P = smt.Function("P", Nat, smt.BoolSort())
kd.kernel.induct_inductive(n, P)
```

&#x22A8;Implies(And(P(Z),
            ForAll(pred!95,
                   Implies(P(pred!95), P(S(pred!95))))),
        P(n))

## Equality

On the principle that Z3 exposed functionality should be rewrapped into Proof manipulating functions, there is a function `subst` <https://github.com/philzook58/knuckledragger/blob/4ecf328b8e0b31c7330ef53102d2812b96522469/src/kdrag/kernel.py#L330> which takes in equality proofs and uses `z3.substitute` in order to replace them everywhere.

A fuller compliment of equational rules involving congruence, transitivity, and reflexivity are kept in a side file. They have not proven themselves to be useful enough to be promoted to the kernel.

```
  |= ta1 = ta2   |= tb1 = tb2    ...
------------------------------------ subst
     |= t = t[ta2/ta1, tb2/tb1, ...]
```

```python
pfxy = kd.kernel.axiom(x == y)
kd.kernel.subst(x + 1, [pfxy])
```

    (y!1 + 1, |= x!0 + 1 == y!1 + 1)

## Structural Rules

It is unfortunate, but seems to be the case that Z3 cannot be relied upon to perform seemingly trivial structural manipulations in the presence of big ocmpliocated terms. For this reason, it is desirable to have a full set of structural rules.
It is very frustrating to have a fully spelled out proof rejected, so these structural rules are in the backwards tactic system.
It is possible that I misplaced my blame on Z3 and there was another problem at play.

I would consider z3 failure on a reasonably sized quantifier free fragment involving theories it strongly supports (like linear inequalities) to be a bug in z3 and have never encountered that. It is quantifiers and lambdas that can sometimes trip it up over even seemingly trivial reasoning.

It has been very tempting to extend `Proof` into a more sequent like form `Gamma |= P` rather than it's current Hilbert like form `|= P`. I don't really think there is that much point ultimately. Judgements with a context can be seen as Hilbert style judgements of a particular forms `|= And(Gamma) -> P` with derived combinators for manipulating them. An important class of combinator is one that reduces the `And` hypothesis such that it has set-like character. Any method for sorting and deduping the `Gamma` terms will work.

There seems to be a pattern for record-like objects about whether to put the record character into the logic or keep it unpacked at the metalevel. The two layers are usually basically interconvertible.

# Bits and Bobbles

I have not written about it systematically in a while. I found this post kind of boring to write, but that is bad. I really need to work towards a systematic presentation of the system and get it on arxiv.

There are more axiom schema scattered throughout domain specific libraries, but the above are the really essential general ones. I continue to push rules into the kernel or pull them out if I never use them really. The churn is not so much at this point though.

More to discuss:

- The rewriting subsystem. I don't think I've ever written a post about this, although it was in the background of my knuth bendix posts
- Modules as an organizing and abstraction principle
- The semantic refinement typing subsystem
- MetaSMT proof certificates
- The backwards tactic system

- Knuckeldragger rules
- Prolog Variations
- Property based testing of refinements
- Rewriting

or  <https://arxiv.org/pdf/cs/9301110> Paulson chapt 10 <https://www.cl.cam.ac.uk/~lp15/MLbook/PDF/chapter10.pdf> (hmm maybe this isn't exactly lcf)
<https://lawrencecpaulson.github.io/2022/01/05/LCF.html>

<https://www.reddit.com/r/ProgrammingLanguages/comments/1aigns2/discussing_isabellehol_a_proof_assistant_for/kova7l5/>
