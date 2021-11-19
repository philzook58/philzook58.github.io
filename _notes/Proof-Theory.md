---
layout: post
title: Proof Theory
---
- <https://en.wikipedia.org/wiki/Proof_theory>
- <https://plato.stanford.edu/entries/proof-theory/>
- <https://plato.stanford.edu/entries/proof-theory-development/>
- Intro to MetaMethemtaics - Kleene
- Basic Proof Theory - Troelstra Schiwtchenberg


Ask Cody.

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
Proof mining. You can take proofs, which are things (annotated trees basically?), and extract interesting content from them.

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

Common axioms schema:
- Induction in Peano Arithemtic

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
## Second Order Arithmetic
"Analysis"
## Robinson Arithmetic (Q)
Weaker than Peano Airthemtic, Induction schema removed. Still a complex thing
## Primitive Recursive Arithmetic
<https://en.wikipedia.org/wiki/Primitive_recursive_arithmetic>
## Set Theory
### ZFC
<https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory>



### Arithmetic Hierarchy
### Undefinability of Truth
### Godel Completeness
### Godel Incompleteness



### Uhhhh
Transfinite induction
Ordinals

<https://github.com/neel-krishnaswami/proof-checker> simple proof checker