---
layout: post
title: Mathematical Logic
---

- [Well formed formula](#well-formed-formula)
- [Lowenheim Skolem](#lowenheim-skolem)
- [Semantic entailment](#semantic-entailment)
- [Soundness](#soundness)
- [Completeness](#completeness)
- [Compactness](#compactness)
- [Consistency](#consistency)
- [Set Theory](#set-theory)
    - [Ordinals](#ordinals)
    - [ZFC](#zfc)
    - [NBG](#nbg)
    - [Axiom of Choice](#axiom-of-choice)
- [Model thoery](#model-thoery)
  - [Finite Model Theory](#finite-model-theory)
    - [Fixed point logic](#fixed-point-logic)
- [Intuitionism / Constructive Math](#intuitionism--constructive-math)
- [Misc](#misc)


https://en.wikipedia.org/wiki/Mathematical_logic
This whole subfolder is about mathematical logic

- Set theory
- Model Theory
- Proof theory
- recursion theory

# Well formed formula



# Lowenheim Skolem 
https://en.wikipedia.org/wiki/L%C3%B6wenheim%E2%80%93Skolem_theorem
For infinite models, there are always bigger and smaller models.


Lindstrom's theorem

https://en.wikipedia.org/wiki/Skolem%27s_paradox Skolem's paradox.
Set theory says there are uncountable sets, but set theory is expressed in countable language


# Semantic entailment
`|=` is used in different ways

`G |= x`. G is a set of formula. This is to say that every model in which G hold, x also holds

`G, not x |= {}` is unsat.

Model's are often treated less carefully. We agree the integers are a thing. Formulas we are sticklers about
Models are shallow embedded, formulas are deep embedded

# Soundness
G |- x  --> G |= x

Syntactic rules are obeyed in models.


# Completeness
G |= x --> G |- x

# Compactness
Infinite families of sentences

Propositional compactness

Infinite graphs?

A proof only uses a finite number of axioms (?)


# Consistency


# Set Theory
Schroder-Bernstein Theorem


Forcing


[hereditarily finite sets](https://en.wikipedia.org/wiki/Hereditarily_finite_set)
set who's elements are also hereditarily finite. set of sets of sets of ... empty set
finitary set theory


non well founded hypersets
https://en.wikipedia.org/wiki/Non-well-founded_set_theory

apg accessible pointed graph https://en.wikipedia.org/wiki/Rooted_graph
Hypersets. Set equations.
Aczel is a computer scientist. 
https://en.wikipedia.org/wiki/Aczel%27s_anti-foundation_axiom

https://en.wikipedia.org/wiki/Axiom_of_regularity aka axiom of foundation


Axiom of specification. Let's us take arbitrary subsets of predefined sets

https://en.wikipedia.org/wiki/Axiom_of_pairing 

Ordered Pairs - part of the general idea of sequences of subsets.

### Ordinals
A well ordered set is a set combined with a well order on it.
Order isomporphic things are the ordinals

A generalizatin of counting or position

Von Neummann, ordinal is the set of all things less than that ordinal.

Ordinals are totally ordered?

[Transfinite induction](https://en.wikipedia.org/wiki/Transfinite_induction)


### ZFC
<https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory>
[Richard Borcherd lectures on zfc](https://www.youtube.com/playlist?list=PL8yHsr3EFj52EKVgPi-p50fRP2_SbG2oi)

### NBG
[Von Neumann–Bernays–Gödel set theory](https://en.wikipedia.org/wiki/Von_Neumann%E2%80%93Bernays%E2%80%93G%C3%B6del_set_theory)

Finite axiomatization? As in no schema? That's crazy.
<https://cstheory.stackexchange.com/questions/25380/which-formalism-is-best-suited-for-automated-theorem-proving-in-set-theory>
<https://cstheory.stackexchange.com/questions/25127/what-paradigm-of-automated-theorem-proving-is-appropriate-for-principia-mathemat>
metamath is all schemata?

### Axiom of Choice
Well ordering principle
Zorn's Lemma https://en.wikipedia.org/wiki/Zorn%27s_lemma
[Choiceless Grapher Diagram creator for consequences of the axiom of choice (AC).](https://cgraph.inters.co/)
Axioms of dependent choice

https://en.wikipedia.org/wiki/Diaconescu%27s_theorem axiom of choice implies excluded middle

Weaker notions
https://en.wikipedia.org/wiki/Axiom_of_countable_choice
https://en.wikipedia.org/wiki/Axiom_of_dependent_choice


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

# Intuitionism / Constructive Math
Choice sequences

https://en.wikipedia.org/wiki/Constructive_set_theory

https://en.wikipedia.org/wiki/Constructive_analysis

# Misc

https://news.ycombinator.com/item?id=33236447

[Book list](https://github.com/jaalonso/Libros_de_Logica/blob/main/README.org)

mathematical logic through python

[Mathematical Logic and Computation - Avigad](https://www.cambridge.org/core/books/mathematical-logic-and-computation/300504EAD8410522CE0C27595D2825A2)

[Handbook of mathemtical logic](http://www.alefenu.com/libri/handbooklogica.pdf)

https://carnap.io/srv/doc/index.md
forall x https://www.fecundity.com/logic/
jscoq, lean-web-editor, sasylf, pie
https://github.com/RBornat/jape



https://home.sandiego.edu/~shulman/papers/induction.pdf
equality as induction.
Defining the axioms of equality as an axiom schema.

https://golem.ph.utexas.edu/category/2013/01/from_set_theory_to_type_theory.html from set theory to type theory
ects - structural set theory. notion of set and function. 

https://golem.ph.utexas.edu/category/2012/12/rethinking_set_theory.html rethinking set theory

