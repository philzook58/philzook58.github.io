---
layout: post
title: Proof Theory
---
- <https://en.wikipedia.org/wiki/Proof_theory>
- <https://plato.stanford.edu/entries/proof-theory/>
- <https://plato.stanford.edu/entries/proof-theory-development/>
- Intro to MetaMethemtaics - Kleene
- Basic Proof Theory - Troelstra Schiwtchenberg
- Boolos Burgess Jeffrey - Computability and Logic
- Minksy - Computation: Finite and Infinite Machines
Ask Cody.

Should I seperate this out into a computability, logic, model theory, and proof theory notes?

# What are Proofs?

# Consistency
<https://en.wikipedia.org/wiki/Consistency>
It is surprisingly subtle and difficult to make a reasoning system in which you don't end up being able to prove everything
A system is consistent if you can't prove "false" in it.


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


## Hilbert systems
<https://en.wikipedia.org/wiki/Hilbert_system>
Many axioms, few rules of inference.
These are often presented as something like a sequence of steps, each being dignified by referring to the results of previous steps


## Sequent Calculus
<https://en.wikipedia.org/wiki/Sequent_calculus>

## Natural Deduction


# Things
## Peano Arithmetic
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

## Robinson Arithmetic (Q)
Weaker than Peano Airthemtic, Induction schema removed. Still a complex thing
## Primitive Recursive Arithmetic
<https://en.wikipedia.org/wiki/Primitive_recursive_arithmetic>
## Set Theory
### ZFC
<https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory>
[Richard Borcherd lectures on zfc](https://www.youtube.com/playlist?list=PL8yHsr3EFj52EKVgPi-p50fRP2_SbG2oi)
### NBG
[Von Neumann–Bernays–Gödel set theory](https://en.wikipedia.org/wiki/Von_Neumann%E2%80%93Bernays%E2%80%93G%C3%B6del_set_theory)

Finite axiomatization? As in no schema? That's crazy.
<https://cstheory.stackexchange.com/questions/25380/which-formalism-is-best-suited-for-automated-theorem-proving-in-set-theory>
<https://cstheory.stackexchange.com/questions/25127/what-paradigm-of-automated-theorem-proving-is-appropriate-for-principia-mathemat>
metamath is all schemata?

### Arithmetic Hierarchy
Formula equivalent to one using some particular combo of quantifiers.
Proof 

<https://en.wikipedia.org/wiki/Tarski%E2%80%93Kuratowski_algorithm> algoirthm to get upper bound. Finding upper bound is easy
Finding lower bound may be hard.

These are considered "sets" because importantly, these are not closed formula. An unclosed formula can be considered a set via the axiom schema of comprehension
### 


### Undefinability of Truth
### Godel Completeness
### Godel Incompleteness


# Interpetability
<https://en.wikipedia.org/wiki/Interpretability>
Reduction of one logic to another.


### Uhhhh
Transfinite induction
Ordinals

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


# Model thoery
[gentle introduction to model theory](https://www.youtube.com/watch?v=xNJHw8E_36g&ab_channel=LambdaConf)
Model theory is more informal?
I have thought model theory is finding what logic looks like in informal set theory
A more general notion and precise notion may be finding homomorphisms between . A way of mapping statements to each other such that theorems in one theory are theorems in the other.