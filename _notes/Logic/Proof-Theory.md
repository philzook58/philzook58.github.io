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
  - [Heyting Arithmetic](#heyting-arithmetic)
  - [PRA (Primitive Reucrsive Arithemtic)](#pra-primitive-reucrsive-arithemtic)
  - [Second Order Arithmetic](#second-order-arithmetic)
  - [Second Order Logic](#second-order-logic)
  - [Robinson Arithmetic (Q)](#robinson-arithmetic-q)
  - [Primitive Recursive Arithmetic](#primitive-recursive-arithmetic)
  - [Set Theory](#set-theory)
    - [ZFC](#zfc)
    - [NBG](#nbg)
    - [Arithmetic Hierarchy](#arithmetic-hierarchy)
    - [](#-1)
    - [Undefinability of Truth](#undefinability-of-truth)
    - [Godel Completeness](#godel-completeness)
    - [Godel Incompleteness](#godel-incompleteness)
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
- [Model thoery](#model-thoery)
  - [Finite Model Theory](#finite-model-theory)
    - [Fixed point logic](#fixed-point-logic)

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

Left and Right rules.
You are breaking down formula going up the inference rule

## Natural Deduction


# Ordinal Analysis
Transfinite induction https://en.wikipedia.org/wiki/Transfinite_induction
Ordinals 
Order theoretic strength
[The Art of Measuring the Strength of Theories](https://www.ams.org/notices/202307/rnoti-p1071.pdf)
[The Curious Dependence of Set Theory on Order Theory ](https://golem.ph.utexas.edu/category/2012/10/the_curious_dependence_of_set.html)

https://en.wikipedia.org/wiki/Ordinal_analysis

Well Ordering

Well ordering principle
Zorn's Lemma https://en.wikipedia.org/wiki/Zorn%27s_lemma
Axiom of Choice
Axioms of dependent choice

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

## Second Order Logic
[](https://plato.stanford.edu/entries/logic-higher-order/)

## Robinson Arithmetic (Q)
Weaker than Peano Airthemtic, Induction schema removed. Still a complex thing
## Primitive Recursive Arithmetic
<https://en.wikipedia.org/wiki/Primitive_recursive_arithmetic>
## Set Theory
Schroder-Bernstein Theorem


Forcing

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

[finite model theory notes dan suciu](https://courses.cs.washington.edu/courses/cse599c/18sp/lectures/unit3-handout.pdf)
## Finite Model Theory
https://homepages.inf.ed.ac.uk/libkin/fmt/fmt.pdf finite model theory book

https://courses.cs.washington.edu/courses/cse599c/18sp/calendar/lecturelist.html
Finite model theory is actually interesting.
Finite models are those for which Z3 can return results even in the prescence of quantifiers.

query containment
```python
from z3 import *
Sort("A")
A = Function("A", BoolSort())
B = 
Q1 = And()
Q2 = And()

contains = ForAll([] , Implies(
  Q1, Q2
))

prove(contains)
```

Directly solving for homomorphisms.
The alice book is insane

https://simons.berkeley.edu/workshops/logical-structures-computation-boot-camp/
https://www.youtube.com/watch?v=rfvYLCixrdQ&ab_channel=SimonsInstitute

### Fixed point logic
https://en.wikipedia.org/wiki/Fixed-point_logic

[Fixed-Point Logics and Computation - Dawar](https://www.cl.cam.ac.uk/~ad260/talks/oviedo.pdf)

Horn clauses interpreted as implications are loose. More models obey than you want. You want the least model. You can fix this (sometimes?) by clark completion and loop formula.

Fixed point logic binds both a second order variable and a et of tuples to it? And it returns another relation that can be applied.

The least fixed point logic is good for datalog.
Greatest fixed point logics include u-calculus.

Thes are both model checking problems.

Translation into datalog

```python
import clingo


```

```ocaml
type prop =  Rel rel * term list
type fof = Forall of fof | Exists of fof | Prop of prop | And | Or | Neg | ... 
type form = Lfp of var list * rel * form | FOF of fof

type rule = {head : prop ; body : prop list} 
type datalog = rule list
let interp : form -> datalog


```

Finite Model Theory and Its Applications - book


Is the empty set a model of fixed point

https://courses.cs.washington.edu/courses/cse344/13au/lectures/query-language-primer.pdf
compiling first order logic model checking to sql or nonrecursive datalog

Ok, but a prolog program might make sense.
Or magic-set/ demand style pushing down seeds from existentials.

Model checking first order logic is a strange thing to do. Model finding or proving are more common things to do I feel like. Although since datbase queries are in some sense model checking.. hmm.

Prolog against a ground database.
All the negation makes me queasy.
```prolog
:- initialization(main,main).

check(and(P,Q)) :- check(P), check(Q).
check(or(P,Q)) :- check(P) ; check(Q).
check(not(P)) :- \+ check(P).
check(forall(D, P)) :-  forall(D, check(P)). % \+ check(exists(X, not(P))).  % %https://www.swi-prolog.org/pldoc/man?predicate=forall/2
check(exists(Y, P)) :- check(P). % , call(D). Perhaps we should check the 
check(pred(P)) :- call(P).
check(implies(P,Q)) :- check(or(not(P), Q)).

% maybe with tabling I can demonstrate
% check(mu(R,X,P)) :- ??
p(1).
q(2).

dom(1).
dom(2).
% sort has to be specified when binding 
main(_) :- print("hi"), check(forall(dom(X), pred(p(X)))).

% This formulation rather than reflecting to primitive prolog at predicates would be literal translation of
% the satisfactin relation
% sat(Formula, Interp) :- 

% models of separation logic required proof.

%q1(X) :- check(exists(Y, and(likes(X,Y), forall(Z, implies(serves(Z,Y), frequents(X,Z)))))).



```

Also probably ASP makes this easier. Use - relation for negation. It's hard to write the interpreter though.

```clingo
% write down database facts

And
existsp(Y,Z) :- p(X,Y,Z).
% forall rule
forallp(Y,Z) :- { p(X,Y,Z) : dom(X) }

negp(X,Y,Z) :- -p(X,Y,Z).

```

Hmm. EPR. But I want satisfiability of EPR, not model checking. Ok. amusing idea, but no.


```sql
-- NOT EXISTS in where clause with subquery.
```


model checking propsitional formula is easy. Plug it in
model checking QBF is harder.

datalog is really model producing. That's kind of the point.

The lfp of lfp(FO) is kind of like the mu minimization operator. https://en.wikipedia.org/wiki/%CE%9C_operator