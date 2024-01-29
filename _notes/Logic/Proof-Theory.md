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

Quotation - see note on macros?

We can encode syntax as a number. The details don't matter that much except you need to be concrete to make sure things are working
<https://en.wikipedia.org/wiki/G%C3%B6del_numbering>
"arithmetization"

Sequences of numbers <https://en.wikipedia.org/wiki/G%C3%B6del_numbering_for_sequences>

inference rules

```python
from z3 import *
import functools
import z3.z3consts as z3consts
Formula = Datatype("Formula")
Formula.declare("FAnd", ("arg0", Formula), ("arg1", Formula))
Formula.declare("FOr", ("arg0", Formula), ("arg1", Formula))
Formula.declare("FNot", ("arg0", Formula))
Formula.declare("FBoolLit", ("arg0", BoolSort()))
Formula.declare("FAtom", ("arg0", StringSort()))
Formula = Formula.create()

# match on z3 ast and return a Formula
# This is a metalevel (python) function that observese syntax
def quote(expr):
  match expr.decl().kind():
    case z3consts.Z3_OP_AND:
      return functools.reduce(Formula.FAnd, map(quote, expr.children()))
    case z3consts.Z3_OP_OR:
      return Formula.FOr(quote(expr.arg(0)), quote(expr.arg(1)))
    case z3consts.Z3_OP_NOT:
      return Formula.FNot(quote(expr.arg(0)))
    case z3consts.Z3_OP_TRUE:
      return Formula.FBool(True)
    case z3consts.Z3_OP_FALSE:
      return Formula.FBool(False)
    case z3consts.Z3_OP_UNINTERPRETED:
      return Formula.FAtom(String(expr.decl().name()))
    case _:
      raise Exception("Unknown", expr)
      
a,b,c = Bools("a b c")
expr = And(a,b,Or(c,Not(c)))
print(quote(expr))

```

Quotation as a theoyr? HOL QE <https://arxiv.org/abs/1802.00405>
"Interesting. They keep things consistent by not allowing eval to occur inside of quotation. This is a kinda like adding T-sentences, that say "the sentence 'P' is true iff P", for each sentence P that doesn't contain the predicate "is true", but at the level of an evaluation rule rather than as a bunch of new axioms.
I wonder what other theories of truth you could lift into evaluation rules?
For modal logic with quotes, there's provability logic, which is a modal logic where the box is supposed to mean "P is provable (in some formal system)". The big adequacy results for that involve translating the box into a first order sentence of arithmetic (or something similar) that you'd write with quasi-quotes (standing for Godel coding)

" - Graham

<https://proofassistants.stackexchange.com/questions/1055/what-provers-are-using-quote-quotations-or-quasiquotations>

lisp-3

<https://plato.stanford.edu/entries/truth-axiomatic/#TSent>
<https://plato.stanford.edu/entries/quotation/>

if we have formula objects, we really can make a relation R over them representing a single step of inference. Then standard translation of modal logic and provability logic

<https://www.lesswrong.com/posts/ALCnqX6Xx8bpFMZq3/the-cartoon-guide-to-loeb-s-theorem> cartoon guide to lob's theorem

### Undefinability of Truth

<https://en.wikipedia.org/wiki/Tarski%27s_undefinability_theorem>

We can godel code statements. We cannot define the subset of coded statements that are true inside our system.

<https://inference-review.com/article/loebs-theorem-and-currys-paradox> Löb’s Theorem and Curry’s Paradox

"Suppose you've got a theory (just like, a first-order one for simplicity, FOL + some designated relations and function symbols maybe, and some axioms. Peano Arithmetic for example), that can represent its own syntax, in some sense, so that you've got a kind of "quotation function" ⌜:black_small_square:⌝ in the metalanguage such that for every sentence φ of the of the theory, there's some term ⌜φ⌝ in the language of the theory (usually built up in some kind of systematic way, like with Godel numbering).
Then Tarskian truth is roughly some predicate T such that T(⌜φ⌝) :left_right_arrow: φ. The English language equivalent is the fact that the sentence "snow is white" is true if and only if snow is white.
For any reasonably strong theory and reasonably simple quotation function, the theory ends up being able to reason enough about quotation that, for every definable predicate ψ of the language of the theory, there's some sentence φ of the language of the theory such that the theory proves φ :left_right_arrow: ψ(⌜φ⌝). (The fact that these biconditionals are always provable is the "diagonal lemma" - Gödel figured it out, Carnap wrote down the general pattern).
You can't define a Tarskian truth predicate in _any model_ of the theory T (this is stronger than just the Tarski biconditionals not being provable).
Suppose you _could_ define a predicate T in some model M of your theory such that, for every sentence φ of the language of T, M satisfies T(⌜φ⌝) :left_right_arrow: φ. Then ¬T(x) would also be a definable predicate, and you'd have a sentence L (for liar) such that ¬T(⌜L⌝) :left_right_arrow: L was provable in T, and satisfied by M. In that situation,
  ¬T(⌜L⌝) ↔ L          (by diagonal lemma)
           ↔ T(⌜L⌝)    (by T a truth predicate)
But ¬T(⌜L⌝) :left_right_arrow: T(⌜L⌝) is unsatisfiable so it can't be true in M. Hence you can't define a predicate T like that.

This gives you a slick non-constructive proof of Godel's first incompleteness theorem. If every truth of arithmetic were provable by PA, then "provable by PA" would be a definable truth predicate in the standard model of PA. But truth isn't definable in the standard model of PA. Therefore, not every truth of arithmetic is provable by PA.
" - graham

### Diagonal Argument

<https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument>

### Godel Completeness

### Godel Incompleteness

<https://arxiv.org/pdf/2104.13792.pdf> A Mechanised Proof of G¨odel’s Incompleteness Theorems using Nominal Isabelle - Paulson

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
