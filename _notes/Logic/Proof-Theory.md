---
layout: post
title: Proof Theory
---

- [What are Proofs?](#what-are-proofs)
- [Consistency](#consistency)
- [Completeness](#completeness)
- [Soundness](#soundness)
- [Structural Proof](#structural-proof)
- [Cut Elimination](#cut-elimination)
- [Interpolation](#interpolation)
- [Reverse Mathematics](#reverse-mathematics)
- [Proof Calculi](#proof-calculi)
  - [](#)
  - [Axioms](#axioms)
    - [Axiom Schemes](#axiom-schemes)
  - [Rules of Inference](#rules-of-inference)
  - [Hilbert systems](#hilbert-systems)
  - [Sequent Calculus](#sequent-calculus)
  - [Natural Deduction](#natural-deduction)
- [Ordinal Analysis](#ordinal-analysis)
- [Things](#things)
  - [Peano Arithmetic](#peano-arithmetic)
    - [Godel numbering](#godel-numbering)
    - [Undefinability of Truth](#undefinability-of-truth)
    - [Diagonal Argument](#diagonal-argument)
    - [Godel Completeness](#godel-completeness)
    - [Godel Incompleteness](#godel-incompleteness)
  - [Heyting Arithmetic](#heyting-arithmetic)
  - [PRA (Primitive Reucrsive Arithemtic)](#pra-primitive-reucrsive-arithemtic)
  - [Second Order Arithmetic](#second-order-arithmetic)
  - [Second Order Logic](#second-order-logic)
  - [Robinson Arithmetic (Q)](#robinson-arithmetic-q)
  - [Primitive Recursive Arithmetic](#primitive-recursive-arithmetic)
    - [Arithmetic Hierarchy](#arithmetic-hierarchy)
    - [](#-1)
- [Interpetability](#interpetability)
  - [Uhhhh](#uhhhh)
  - [Computability theory](#computability-theory)
  - [Binders](#binders)
    - [Mu operator](#mu-operator)
    - [epsilon operator](#epsilon-operator)
    - [forall](#forall)
    - [exists](#exists)
    - [exists unique](#exists-unique)
    - [Bounded quantification](#bounded-quantification)
    - [lambda](#lambda)
  - [recursion/fixpoint binder](#recursionfixpoint-binder)
    - [comprehesion](#comprehesion)
    - [modal operators](#modal-operators)
    - [Of a different character?](#of-a-different-character)

Should I seperate this out into a computability, logic, model theory, and proof theory notes?

<https://en.wikipedia.org/wiki/Proof_theory>

# What are Proofs?

# Consistency

<https://en.wikipedia.org/wiki/Consistency>
It is surprisingly subtle and difficult to make a reasoning system in which you don't end up being able to prove everything
A system is consistent if you can't prove "false" in it.

Systems can't prove themselves consistent (?) You need more "power"

Gentzen proved peano arith consistent <https://en.wikipedia.org/wiki/Gentzen%27s_consistency_proof>

# Completeness

# Soundness

# Structural Proof

# Cut Elimination

# Interpolation

# Reverse Mathematics

<https://en.wikipedia.org/wiki/Reverse_mathematics>
Proof mining. You can take proofs, which are things (annotated trees basically?), and extract interesting content from them.

Determine which axioms are required to prove theorems.
Often subsystems of second order arithmetic (peano arithmetic with set objects)

# Proof Calculi

<https://en.wikipedia.org/wiki/Proof_calculus>

###

### Axioms

#### Axiom Schemes

<https://en.wikipedia.org/wiki/Axiom_schema>
Axiom schemes are axioms that have pattern variables in them that stand for arbitrary formula. They represent an infinite class of axioms.

They can be represented as `Formula -> Bool`, a checker that the formula you give is an instance of the schema. Or to make life even easier for your checker `Bindings -> Formula -> Bool`.
In principle they may also be represented as `Stream Formula` a possibly infinite stream of formula, but this is inconvenient to wait until you get the formula you want.
All of these things are _actually_ not the same. The first is saying it is decidable whether a formula is an instance of the axiom schema, the second is saying it is semidecidable. Maybe the second is not actually an axiom schema.

Common axiom schema:

- Induction in Peano Arithemtic
- Set comprehension

Axiom schema are sort of a macro system thing that lets you avoid second order logic

### Rules of Inference
<https://en.wikipedia.org/wiki/Logical_harmony> logical harmony. See notes of frank pfenning

## Hilbert systems

<https://en.wikipedia.org/wiki/Hilbert_system>
Many axioms, few rules of inference.
These are often presented as something like a sequence of steps, each being dignified by referring to the results of previous steps

## Sequent Calculus

<https://en.wikipedia.org/wiki/Sequent_calculus>

Left and Right rules.
You are breaking down formula going up the inference rule

## Natural Deduction

# Ordinal Analysis

Transfinite induction <https://en.wikipedia.org/wiki/Transfinite_induction>
Ordinals
Order theoretic strength
[The Art of Measuring the Strength of Theories](https://www.ams.org/notices/202307/rnoti-p1071.pdf)
[The Curious Dependence of Set Theory on Order Theory](https://golem.ph.utexas.edu/category/2012/10/the_curious_dependence_of_set.html)

<https://en.wikipedia.org/wiki/Ordinal_analysis>

Well Ordering

# Things

## Peano Arithmetic

Axiom schema vs second order axiom.

Or are you in a second order system and tracking
Are peano axioms conditions for an embedding in a larger system, or are hey

Peano embedded in term of ZF theory.

```lean
inductive pterm where
  | Add : pterm -> pterm -> pterm
inductive pform where
  | Eq : pterm -> pterm -> pform
  | 
inductive pproof where
 | Induct : (pterm -> pform) -> 

```

```python
from z3 import *
# Z3py adt of natural numbers
Nat = Datatype("Nat")
Nat.declare("zero")
Nat.declare("succ", ("pred", Nat))
Nat = Nat.create()
#Nat = Datatype("Nat", ["zero", "succ"])
print(Nat.succ(Nat.zero))

def induct(P):
  # assert P.type == Nat -> Bool ?
  n = FreshConst(Nat)
  return ForAll(n, Implies(P(Nat.zero), Forall(n, Implies(P(n), P(Nat.succ(n))))), Forall(n, P(n)))

inj = Function("inj", Nat, IntSort())
n = FreshConst(Nat)
axioms = [
  inj(Nat.zero) == 0,
  ForAll(n, inj(Nat.succ(n)) == inj(n) + 1) # recursive definition of inj
]

theorem1 = ForAll(n, inj(n) >= 0)
theorem2 = ForAll(i, Implies(i >= 0, Exist(n, inj(n) == i)))
P = lambda x: 

```

```python
from z3 import *



def Peano():
  def __init__(self):
    self.data = {}
    self.defns = {}
  def induction(self, name, P): # make n a parameter?
    n = FreshInt() # make n a nat?
    self.data[name] = Implies(And(P(0), Forall([n],Implies(P(n), P(n+1)))), ForAll(n, P(n)))
  def theorem(self, name, th, *lemmas):
    assert name not in self.data
    s = Solver()
    for lemma in lemmas:
      s.add(self.data[lemma][1])
    s.add(Not(th))
    res = s.check()
    if res == unsat:
      self.data[name] = ("theorem", th, lemmas)
    elif res == sat:
      print(s.model())
      raise Exception("Not a theorem")
    else:
      raise Exception("Unknown")
  def definition(self, name, args, res, th):
    assert name not in self.defns
    self.theorem(name + "_total", ForAll(args, Exist(res, th)))
    self.theorem(name + "_unique", ForAll(args, Forall([res, res2], Implies(And(th, th2), res == res2))))
    self.defns[name] = (args, res, th)
    self.data = ("definition", )
    #self.data[name] = ("definition", th)
  def axiom(name, th):
    self.data[name] = ("axiom", th)





```

### Godel numbering

We can encode syntax as a number. The details don't matter that much except you need to be concrete to make sure things are working
<https://en.wikipedia.org/wiki/G%C3%B6del_numbering>
"arithmetization"

Sequences of numbers <https://en.wikipedia.org/wiki/G%C3%B6del_numbering_for_sequences>

inference rules

### Undefinability of Truth

<https://en.wikipedia.org/wiki/Tarski%27s_undefinability_theorem>

We can godel code statements. We cannot define the subset of coded statements that are true inside our system.

### Diagonal Argument

<https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument>

### Godel Completeness

### Godel Incompleteness

## Heyting Arithmetic

## PRA (Primitive Reucrsive Arithemtic)

Equivalent to Godel's system T? People tend to imply lambda binders available when discussing T

Gentzen's consistency proof reduced peano arithmetic to PRA

<https://en.wikipedia.org/wiki/LOOP_(programming_language)>
<https://plato.stanford.edu/entries/recursive-functions/>

Axiom schema of induction but only over unquantified formula.
All the axiom can be expressed in unquantified logic?

In a sense, because quantifier free, theorems are all universally quantified.

## Second Order Arithmetic

"Analysis"
Two sorts, natrual numbers a la peano and sets of natural numbers

A comprhenesion axiom schema and inducton axioms schema

Subsystems of second order arithmetic - simpson
[The Prehistory of the Subsystems of Second-Order Arithmetic](https://arxiv.org/pdf/1612.06219.pdf)

## Second Order Logic

[](https://plato.stanford.edu/entries/logic-higher-order/)

## Robinson Arithmetic (Q)

Weaker than Peano Airthemtic, Induction schema removed. Still a complex thing

## Primitive Recursive Arithmetic

<https://en.wikipedia.org/wiki/Primitive_recursive_arithmetic>

### Arithmetic Hierarchy

Formula (logically) equivalent to one using some particular combo of quantifiers.

Logically equivalent is with respect to a particular model.

Proof

<https://en.wikipedia.org/wiki/Tarski%E2%80%93Kuratowski_algorithm> algoirthm to get upper bound. Finding upper bound is easy. Basically, convert the formula to prenex form (put quantifiers in front). This can be done algorithmically.
Finding lower bound may be hard.

These are considered "sets" because importantly, these are not closed formula. An unclosed formula can be considered a set via the axiom schema of comprehension

###

# Interpetability

<https://en.wikipedia.org/wiki/Interpretability>
Reduction of one logic to another.

### Uhhhh

<https://github.com/neel-krishnaswami/proof-checker> simple proof checker

### Computability theory

<https://en.wikipedia.org/wiki/Computability_theory>

## Binders

Many of this can be compiled to equivalent formula involving

### Mu operator

Minimization operator.
The least such that.
<https://en.wikipedia.org/wiki/%CE%9C_operator>

### epsilon operator

Hilbert Choice.

### forall

### exists

### exists unique

### Bounded quantification

### lambda

## recursion/fixpoint binder

In type theory, we want to talk about recursive types. We use a fixpoint binder. How does this relate to logic?
Least fixed point? Greatest?
<https://www.cl.cam.ac.uk/~ad260/talks/oviedo.pdf>
Fixed point logic

### comprehesion

You _could_ consider $\{x | phi(x) \}$ it's own kind of binder

### modal operators

### Of a different character?

Sum, product, min, argmin, integral
If I understand the history, Boole arithmetized logic and the exists and forall operators were actually inspired by actual sum and product
