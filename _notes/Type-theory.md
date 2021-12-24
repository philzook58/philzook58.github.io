---
layout: post
title: Type Theory
---
# Syntax and Semantics

Type theory takes syntax more seriously than I ever realize.
It's like drawing a house. Do you draw a box with a triangle over it, or do you really look.

# Judgement
These are something you can write on paper that represents "I know this". This is where your mind meets the paper in some sense.

Examples:
- Has type $\Gamma \turnstile t : T$
- Is well formed 
- Is Type $\Gamma \turnstile 
- evaluates to (big step/small step) $(1 + 3) \downarrow 4$ or $(1+3) \rightarrow 4$
- Hoare logic step `{true}x := 3{x > 0}`
- Sequent. Under the assumption A,B hold, A holds. $A,B |- A$
- Focused Sequent. Kind of fishy that this has intuitive meaning
- Type synthesizes, Type Checks - In bidirictional typing discipline, a type being synthesizable/inferrable from the term vs a type being checkable given both type and term are distinct judgements.


# Inference Rules
These are the things drawn with horizontal lines. They take you from 

Examples


Concrete computer encodings of judgements and inference rules
- Coq inductive types
- Prolog programs (Twelf is related I think)
- Ocaml/Haskell/python functions. There are many different modes you might pick. You can choose
- Tactics



# Computation Rules

I don't know what this means really. Whatever it means, probably beta reduction (applying lambda functions) is included.

The central idea I think is that if you're building a theorem prover, it needs to understand how to do something. The hypothesis is that it is useful and flexible for the theorem prover to understand well behaved operations of lambda calculus. Lambda calculus has it's origin as a study of pure logic. It hopefully is capable of expressing anything that belongs to our intuitive notion of "algorithm" (again this was what it was invented for).

So we might want to build in knowing how to add numbers or do sines or cosines or something into our theorem prover, but we can usefully encode these concepts into the master concepts of lambda calculus.

I am ultimately not convinced or unconvinced this hypothesis holds and wonder if the mainstream of interactive theorem proving isn't a little too attached to the idea.

### Conversion vs Reduction vs Expansion

Coq may have it's own idiosyncratic naming for different kinds of reduction rules. <https://coq.inria.fr/refman/language/core/conversion.html>

- `(fun x => x ) q ~> q` beta conversion
- `(fun x => x) ~> (fun z => z)` alpha conversion, aka dummy index rewriting
- `match () with () => z  ~> z` match conversion
- `let x := 3 in x ~> 3` zeta reduction
- if `Definition foo := 3.` then `foo ~> 3` delta reduction/unfolding of definitions
- `f ~> (fun x => f x)`, eta conversion. expanding ou
- `x ~> match x with tt => x end` Is this right? This is eta for `unit`

I think eta conversion is the most confusing and puzzling out of all of them. Sometimes eta may refer to only eta expanding functions, but other times it may be referring to the relationship of a data type with it's match statement.

In some sense functions are very special datatypes. They are not defined via an `Inductive` definition. But they are also can be thought of as being kind of similar to these data types. The "constructor" of a function is a lambda binder, and the "eliminator" is an application.
We can encode data types into functions using church like encodings.
`match` can be encoded by positing a special function that has a computation rule like match.






### Consistency
### Progress
### Preservation, Subject Reduction
Evaluation does not cause types to change.
### Normalization
### Completeness
### Soundness


### Head Normal Form
### Value
<https://ice1000.org/2019/04-07-Reduction.html>

#### Neutral
#### Canonical

### Reducible Expression



### Curry vs Church style


# Equality
### Extensional vs Intensional
Extensional equality collapses definitional and propositional equality.

Adding a rule

```
Gamma |- t : Id_Type A B
------------------------
Gamma |- A = B
```
Notice that this is a transition from a typing judgement to a definitional equality judgement. Very different fellas.

### Judgemental/Definitional / Propositional
<https://coq.inria.fr/refman/language/core/conversion.html#conversion-rules> 
<https://coq.inria.fr/refman/proofs/writing-proofs/equality.html>


Another way of talking about judgementally equal is if the proof of Prop equality is just `eq_refl`. Why is this? Well, type checkeing more or less must look for an inferrance rule with `eq_refl : a = b` below the horizontal line. This rule breaks apart this problem into a definitional. Definitional equality is so in the air we breath, it may not even be noted explicitly. Any nonlinear occurence of pattern variables in the inferrence rule must imply it.


Tests. Example `Definition mytest : tt = tt := eq_refl.` See if coq accepts it <https://coq.vercel.app/scratchpad.html>
- `tt = tt`
- `unit = unit`
- `1 + 1 = 2`
- `x : nat |- x + 0 = x`
- `x : nat |- 0 + x = x`
- `(fun x => x) = (fun x => x)`
- `(fun x => x) = (fun x => tt)`
- `(match tt with tt => tt end) = tt`
- `x : unit |- tt = x`
- `x : unit |- match x with () => () end = ()`
- `x : unit |- match x with () => () end = x`
- `x : unit |- match x with () => () end = match x with _ => () end`
- `f |- f = (fun x => f x)` eta
- `(fun x => x) tt = tt`    beta




### Sorts 
<https://coq.inria.fr/refman/language/core/sorts.html>
- Prop vs Type vs Set - Prop is impredicative. Prop and Set are deleted during extraction? Which make them interestingly different from a metaprogramming perspective.

`Prop` `SProp` `Set`
`SProp` is Prop with proof irrelevance
#### Impredicative vs Predicative
This is describing allowing some kind of form of self reference I think.
#### Proof Irrelevance
Propositional extensionality implies proof irrelevance
https://coq.inria.fr/library/Coq.Logic.ProofIrrelevance.html
Axiom proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.

#### Universes
<https://github.com/jdolson/hott-notes/blob/pdfs/pdfs/notes_week5.pdf>
Universes are 

Algerbaic universes - If the levels of type are a DAG, they can be ordered. So one doesn't eagerly pick integer levels for Type. Instead you maintain contraints like max{l1,l2} etc.




### Extensionality
Extensionality is a notion that applies to more than just function and equality types.
https://cstheory.stackexchange.com/questions/17636/%CE%B7-conversion-vs-extensionality-in-extensions-of-lambda-calculus

forall x, f x = g x -> f = g
forall A B : Prop, A <-> B -> A = B
forall x, x = match x with () -> ()

Consider 
fun x -> x = fun x -> tt
Is this provable?

Some of these are provable

alpha
beta
eta
iota



Computational Content

Heterogenous vs Homogenous equality

Eta equivalence - The dumb expansion? Observational Equivalence

Reduction vs Equivalence


### Univalence
Implies extensionality
Example `unit' = unit`
Isomorphisms










# Coq
- QED does something serious.
- Surface coq is desugared
- match annnotations are 
- Note that the judgement `a : A, b : B, c : C |- f : F` is sort of getting Coq to accept `Definition foo (a : A) (b : B) (c : C) : F := f.` It sort of reorders the pieces and make you give a name to the whole judgement `foo`. That's an interesting way of looking at it anyway. Of course the more usual way is that `foo` is a function definition.




- <https://counterexamples.org/title.html> Counterexamples in Type Systems. Really cool resources of problems that can show up in type systems
- <https://github.com/FStarLang/FStar/issues/360> Examples that show paradoxes when using combinations of impredicative polymorphism + excluded middle + large elimination -- can only choose two <https://cstheory.stackexchange.com/questions/21836/why-does-coq-have-prop/21878#21878> Berardi's paradox
<https://github.com/coq/coq/issues/9458> future of impredicative set

## Books:
- TAPL
- Programming Language Foundations - Harper
- Programming in Martin Lof Type Theory
- Software Foundations
- PLFA

# System T
- [Harper Class notes](https://www.andrew.cmu.edu/course/15-312/recitations/rec3-notes.pdf)
- [Girard Proofs and Types](http://www.paultaylor.eu/stable/prot.pdf)
- <https://gregorulm.com/godels-system-t-in-agda/>
- [Avigad Feferman Dialectica](https://www.andrew.cmu.edu/user/avigad/Papers/dialect.pdf)

"Quantifier free theory of functionals of finite type"

# Logical Relations
- [History of programming course](https://felleisen.org/matthias/7480-s21/22.pdf) <https://felleisen.org/matthias/7480-s21/lectures.html> Mentions Amal thesis as being good
- [Intro to logical relations](https://www.cs.uoregon.edu/research/summerschool/summer16/notes/AhmedLR.pdf)

Tait proved strong normalization using them 1967.

Parametricity is supposedly an example also

# Realizability



[Cody's suggested book TOC](https://twitter.com/codydroux/status/1470121974655500293?s=20)
Extensional vs Intensional models?
Chapter 1: The type theory and its variants:
1. The CIC with universes
2. Recursors vs guarded fixpoints
3. Predicative variant
4. Untyped conversion
5. Some additional conversion rules
6. Extensionality principles
7. Anti-extensionality principles
8. Coinduction
Chapter 2: Theorems about syntax
1. Substitution, weakening
2. Well-sortedness
3. Progress and preservation
4. Uniqueness of types(?)
5. Properties of normal forms
Chapter 3: Extensional models
1. The not-so-simple set theoretic interpretation
2. Models of sets in types
3. The effective topos interpretation
4. The groupoid interpretation
5. Consistency implications
Chapter 4: Intensional models
1. Realizability interpretations
2. The Lambda-set model
3. The normalization proof
5. Consistency implications
Chapter 5: Inconsistent combinations of rules
1. Failures of subject reduction
2. Failures of termination *alone*
3. Impredicative inconsistencies
4. Guard condition and inductive type issues
5. Other universe issues


[smalltt](https://github.com/AndrasKovacs/smalltt) a demo for high performance type theory elaboration. Really good readme too
[elboration seminar](https://www.youtube.com/playlist?list=PL2ZpyLROj5FOt99f_KCxARvd1hDqKns5b)
[learn type theory](https://github.com/jozefg/learn-tt)