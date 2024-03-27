---
layout: post
title: Mathematical Logic
---

- [Motivations](#motivations)
- [Generic Concepts](#generic-concepts)
  - [Three Arrows](#three-arrows)
- [Propositional Logic](#propositional-logic)
- [First Order Logic](#first-order-logic)
  - [WFF](#wff)
  - [Quantifiers](#quantifiers)
  - [Semantic entailment](#semantic-entailment)
  - [Soundness](#soundness)
  - [Completeness](#completeness)
  - [Lowenheim Skolem](#lowenheim-skolem)
  - [Compactness](#compactness)
  - [Consistency](#consistency)
- [Equational Logic](#equational-logic)
- [Set Theory](#set-theory)
  - [Families of sets](#families-of-sets)
    - [Ordinals](#ordinals)
    - [Axiom of Choice](#axiom-of-choice)
    - [Forcing](#forcing)
  - [Axiomatizations](#axiomatizations)
    - [ZFC](#zfc)
    - [NBG](#nbg)
    - [Grothendieck Tarksi](#grothendieck-tarksi)
    - [New Foundations](#new-foundations)
  - [Filters](#filters)
- [Model thoery](#model-thoery)
  - [Finite Model Theory](#finite-model-theory)
    - [Fixed point logic](#fixed-point-logic)
- [Intuitionism / Constructive Math](#intuitionism--constructive-math)
- [Proof Theory](#proof-theory)
- [Recursion Theory](#recursion-theory)
  - [Combinators](#combinators)
  - [Lambda Calculus](#lambda-calculus)
    - [Untyped](#untyped)
    - [Typed](#typed)
- [Misc](#misc)

<https://en.wikipedia.org/wiki/Mathematical_logic>
This whole subfolder is about mathematical logic

- Set theory
- Model Theory
- Proof theory
- recursion theory

# Motivations

Euclidean Geometry

<https://plato.stanford.edu/entries/logic-firstorder-emergence/>

Arithmetic, Algebra, Calculus. Highly developed but nonrigorous by modern standards. Logic is highly genralized algebra

Boole
Quantifiers. They really do have histrocial roots in sums $\Sigma$ and products $\Pi$.

The _really_ infinite. Not just bigger and bigger finite things. The closure. Naive set theory emerged in the late 1800s. THere is way more structure in the infinite than might be assumed from simple limit notions in calculus. Considering the infinite as a legitimate entity is akin to considering 0, the negative numbers, complex numbers, non-euclidean geometry as legitamate entities with their own rules. It is quite easy to lead yourself astray without carefulness. Perhaps half of mathematics is fixated on the infinite, something which has close to little application.

Russell's Paradox
Hilbert's Program

# Generic Concepts

syntax
semantics
completeness
soundness
consistency

inference rules
axiom schema

## Three Arrows

[Why are in this system _three_ notions of “from this follows that” involved: the arrow, the turnstile and the vertical line? Two or infinitely many I could accept, but why _three_?](https://x.com/freekwiedijk/status/1717470234087407984?s=20)
<https://x.com/yandereidiot/status/1752749605891326449?s=20> "It's cute to me how self-contained this example is in terms of teasing out the notion of "external hom (2)", "internal hom (3)", and whether or not they play nicely together "adjunction (1)"."
(|-) is external hom, (=>) is internal hom, (---) is a meta-level operation.

- I think there's kinda a literature (keyword: "metainference") about internalizing the (horizontal?) line as yet another symbol: <https://davewripley.rocks/papers/imst.pdf>, section 2 has the basic idea. Infinite hierarchies aplenty. This is probably a better reference, but it seems to be paywalled: <https://link.springer.com/article/10.1007/s10992-021-09615-7>
- possibly related, that lower category theory also has three levels: category, functor, natural transformation.
Yes! But s/category/morphism
Or: number, function, functional."
- @freekwiedijk Natural deduction can be formulated to have only two (cf Schroeder-Heister, and that's how Isabelle does it). But proof normalisation is simpler for the sequent calculus
k An inference line lets you write (to the right) a reference and leave the work to the reader. Frege who came up with the original turnstile in his ConceptScript, also introduced this inference line shorthand (but with the reference to the left
- reekwiedijk They control where implicit quantification occurs. The turnstile is implicitly wrapped in a universal quantifier for any free variables you have. If you do that yourself, you only need "=>" (and the inference rule modus ponens), and it's called Hilbert deduction.
- freekwiedijk (|-) is external hom, (=>) is internal hom, (---) is a meta-level operation
- "meta-level (rules), theory level (judgments), internal level (implications) you can have as many as you want if your brain is big enough to handle more levels. for instance talking about proof theories _inside_ a theory will necessitate four levels!"

# Propositional Logic

<https://en.wikipedia.org/wiki/Propositional_calculus>
Sentential Logic. 0th order

Truth tables
Completeness
Compactness - infinite formula. Why? How infinite?
Intuitionistic prop logic

```lean
-- just a sketch. Doesn't compile.
-- wff.
inductive Prop0 where
  Atom : String -> Prop0
  Impl : Prop0 -> Prop0 -> Prop0

-- Every expressible formula is good.
def wff : Set Prop0 := fun x => True

-- starting from strings. Note that the above Prop0 and the parse proof tree are quite similar.
inductive wff' : String -> Prop
  | atom : forall x, is_ascii x -> wff' x
  | impl : (x y : String) -> wff' x -> wff' y -> wff' (x ++ " -> " ++ y)

def Env := String -> Bool

-- a semantic function
def sem prop env : Bool :=
  match prop with
  | Atom s => env s
  | Impl x y => sem x env -> sem y env 
-- a semantic relation
-- inductive sem : Prop0 -> Env -> Bool -> Prop where

```

```metamath

```

```z3
; deep embedded vampire
(declare-sort Formula)
(declare-fun atom (String) Formula)
(declare-fun impl (Formula Formula) Formula)
()

```

Categorical Flavored  
Double line is fun metalevel "equality" / biimplication
Solvers are nice for determining which axiom sets are equivalent.

```
a /\ b |- c
===========
a |- b => c
```

Could be written as

```
a /\ b |- c = a |- b => c
```

Proof relevance vs irrelevance. LCF style vs Proof carrying style.

Hilbert style
Interpolation

Logical equivalence - kind of a bad name. A semantic notion of equivalence
Conservative extension. Adding in new propositions.
Equisatisfiability - two formulas are equisatisfiable if one is satisfiable iff the other is satisfiable. Could involve changing the signature. Are two unsatsfiable things equisatsifiable?

There isn't a global universal notion of comparing two theories or systems. The comparison is a defined entity. It gets confusing when the two systems seem nearly the same (signatures that are subsets of each other, sharing inference rules). We could talk about `<->` being the same as `/\` in some other system, or made up names like pirate ship. You need to always specify a universe of discourse basically.

Mathemtival logic is tryng to look past your intuition to see the formal symbol moving systems as they are. But contradictorily, these systems are only interesting because they correspond to some form of intuition or philosophical notions. Unless you're just a symbol crunching psycho.

# First Order Logic

Framework vs logic vs theory. Is there a distinction?
Chris once corrected me saying FOL is a framework. Some useful syntactic infrastrcture for talking about / embedding more interesting theories (and getting various theorem proving strategies). However, it appears by completeness and lowenheim skolem to be intmiately related to sets. So perhaps FOL is a kind of weak theory of sets or a weak theory of comprehensions (like taking python comprehensions and allowing them to be highly (uncountably) infinite).

<https://math.stackexchange.com/questions/176263/is-first-order-logic-fol-the-only-fundamental-logic?rq=1>

EPR (effectively propositional reasoning)
Many sorted, order sorted

[Formalizing Basic First Order Model Theory - Harrison](https://www.cl.cam.ac.uk/~jrh13/papers/model.html)

## WFF

## Quantifiers

## Semantic entailment

`|=` is used in different ways

`G |= x`. G is a set of formula. This is to say that every model in which G hold, x also holds

`G, not x |= {}` is unsat.

Model's are often treated less carefully. We agree the integers are a thing. Formulas we are sticklers about
Models are shallow embedded, formulas are deep embedded

## Soundness

G |- x  --> G |= x

Syntactic rules are obeyed in models.

## Completeness

G |= x --> G |- x

## Lowenheim Skolem

<https://en.wikipedia.org/wiki/L%C3%B6wenheim%E2%80%93Skolem_theorem>
For infinite models, there are always bigger and smaller models.
This is possibly a failure of expressivity of FOL, similar in flavor to the inability to express transitivity precisely.

Lindstrom's theorem

<https://en.wikipedia.org/wiki/Skolem%27s_paradox> Skolem's paradox.
Set theory says there are uncountable sets, but set theory is expressed in countable language

Lowenheim spoke of "counting formulae". Perhaps one can try to "perform" the sums and products with the result being cardinals.

Herbrandization and skolemization. These processes change the signature (constants / function symbols) at play, so they can't be strongly equivalent. They work at the level of conservative extensions.

```
T |- phi_s  <-> T |- phi
T_h |- phi  <-> T |- phi

```

## Compactness

Infinite families of sentences

Propositional compactness

Infinite graphs?

A proof only uses a finite number of axioms (?)

## Consistency

# Equational Logic

See also note on term rewriting
Algebra

Equational logic is about simple equational manipulations.
FOL has a first class notion of universal quantification. Equational logic instead has a schematic notion of universal. Axioms can have variables in them which are distinct from 0-ary constants

# Set Theory

mahlo
inaccessible cardinals. axiom of reaplcement
grothendieck
universes

Books:
Halmos Naive Set Theory
Jech Introduction

```python
from z3 import *
S = DeclareSort("Set1")
empty = Const("empty", S)
elem = Function("elem", S, S, BoolSort())
x,y,z = Consts("x y z", S)
power = Function("P", S, S)
sub = Function("sub", S, S, BoolSort())
union = Function("U", S, S, S)
inter = Function("N", S, S, S)


class Theory():
  def __init__(self):
    self.ax = {}
    self.theorem = {}
    # self.kb = {}
  def axiom(self, name, formula):
    self.ax[name] = formula
    self.theorem[name] = formula
  def theorem(self, name, formula, lemmas):
    assert name not in self.theorem
    s = Solver()
    s.add(lemmas)
    s.add(Not(formula))
    res = s.check()
    if res == unsat:
      self.theorem[name] = formula
    else:
      print("Theorem {} is not valid".format(name))
  def define(name, formula):
    c = FreshConst(name,S)
    self.theorems[name + "_define"] = c == formula
    # axiom? theorem?
  def spec(A,P): # axiom of specification
    y = FreshConst(S)
    return ForAll([x], And(elem(x,A), elem(x, P(x))) == elem(x, y))

ZF = Theory()
ZF.axiom("empty", ForAll([x], Not(elem(x, empty))))
ZF.axiom("ext", ForAll([x,y], ForAll([z], elem(z,x) == elem(z,y)) == (x == y)))

ZF.theorem("empty_unique", ForAll([y], Implies(ForAll([x,y], Not(elem(x, y))), y == empty), [])


```

Schroder-Bernstein Theorem

[hereditarily finite sets](https://en.wikipedia.org/wiki/Hereditarily_finite_set)
set who's elements are also hereditarily finite. set of sets of sets of ... empty set
finitary set theory

non well founded hypersets
<https://en.wikipedia.org/wiki/Non-well-founded_set_theory>

apg accessible pointed graph <https://en.wikipedia.org/wiki/Rooted_graph>
Hypersets. Set equations.
Aczel is a computer scientist.
<https://en.wikipedia.org/wiki/Aczel%27s_anti-foundation_axiom>

<https://en.wikipedia.org/wiki/Axiom_of_regularity> aka axiom of foundation

Axiom of specification. Let's us take arbitrary subsets of predefined sets. We need to convert

<https://en.wikipedia.org/wiki/Axiom_of_pairing>

Ordered Pairs - part of the general idea of sequences of subsets.

It is interesting that induction and recursion are principles/theorems and not axioms of set theory. We can use comprehension to find the minimal set that is closed under
Induction
The recursion theorem. A sequence of equations feel like they define a function. Using the principle of specification, we can define get a set of tuples that satisfy the equations. Being a function requires covering the domain and uniqueness of the output. These are theorems that must be proved. It turns out that simple recursion over naturals does define a function.

Peano inside set theory.

## Families of sets

indexed sets

### Ordinals

A well order is a total order such that every nonempty subset has a least element.

A well ordered set is a set combined with a well order on it.

Order isomporphic things are the ordinals

A generalizatin of counting or position. In programming, it does come up whether we can index into a type. An infinitary generalization of this

Von Neummann, ordinal is the set of all things less than that ordinal.

Ordinals are totally ordered?

In some sense, successor + "limits" generates ordinals
<https://en.wikipedia.org/wiki/Successor_ordinal> successor ordinal is smallest ordina larger. constructed as $a \cup \{a\}$ in von neuamann
limit ordinal <https://en.wikipedia.org/wiki/Limit_ordinal> neither zero nor successor ordinal. For every ordinal a less than g, there is an ordinal b between a and g.

[Transfinite induction](https://en.wikipedia.org/wiki/Transfinite_induction)

<https://en.wikipedia.org/wiki/Von_Neumann_universe> von neumann universe. The class of all hereditarily well founded sets
Rank - smallest ordinal greater than all members of set

Burali Forti paradox. Related to Type in Type

<https://math.stackexchange.com/questions/1343527/principle-of-transfinite-induction?rq=1>
The ordinals are what you get when you use successor and supremum indefinitely

### Axiom of Choice

Well ordering principle
Zorn's Lemma <https://en.wikipedia.org/wiki/Zorn%27s_lemma>
[Choiceless Grapher Diagram creator for consequences of the axiom of choice (AC).](https://cgraph.inters.co/)
Axioms of dependent choice

<https://en.wikipedia.org/wiki/Diaconescu%27s_theorem> axiom of choice implies excluded middle

Weaker notions
<https://en.wikipedia.org/wiki/Axiom_of_countable_choice>
<https://en.wikipedia.org/wiki/Axiom_of_dependent_choice>

### Forcing

Continuum hypothesis

<https://xavierleroy.org/CdF/2018-2019/7.pdf> Forcing : just another program transformation? Leroy

Timothy Chow beginner's guide to to forcing <http://timothychow.net/forcing.pdf>

## Axiomatizations

### ZFC

<https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory>
[Richard Borcherd lectures on zfc](https://www.youtube.com/playlist?list=PL8yHsr3EFj52EKVgPi-p50fRP2_SbG2oi)

### NBG

[Von Neumann–Bernays–Gödel set theory](https://en.wikipedia.org/wiki/Von_Neumann%E2%80%93Bernays%E2%80%93G%C3%B6del_set_theory)

Finite axiomatization? As in no schema? That's crazy.
<https://cstheory.stackexchange.com/questions/25380/which-formalism-is-best-suited-for-automated-theorem-proving-in-set-theory>
<https://cstheory.stackexchange.com/questions/25127/what-paradigm-of-automated-theorem-proving-is-appropriate-for-principia-mathemat>
metamath is all schemata?

### Grothendieck Tarksi

### New Foundations

## Filters

<https://math.uchicago.edu/~may/REU2018/REUPapers/Higgins.pdf>
Filters are collections of sets closed under subset and finite intersection
Ultrafilters are filters for which either a set or it's complement are in the filter
A notion of largeness is being nside an ultrafilter

Relation to hypperreals / non standard analysis
compactness

# Model thoery

[gentle introduction to model theory](https://www.youtube.com/watch?v=xNJHw8E_36g&ab_channel=LambdaConf)
Model theory is more informal?
I have thought model theory is finding what logic looks like in informal set theory
A more general notion and precise notion may be finding homomorphisms between . A way of mapping statements to each other such that theorems in one theory are theorems in the other.

[finite model theory notes dan suciu](https://courses.cs.washington.edu/courses/cse599c/18sp/lectures/unit3-handout.pdf)

## Finite Model Theory

<https://homepages.inf.ed.ac.uk/libkin/fmt/fmt.pdf> finite model theory book

<https://courses.cs.washington.edu/courses/cse599c/18sp/calendar/lecturelist.html>
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

<https://simons.berkeley.edu/workshops/logical-structures-computation-boot-camp/>
<https://www.youtube.com/watch?v=rfvYLCixrdQ&ab_channel=SimonsInstitute>

### Fixed point logic

<https://en.wikipedia.org/wiki/Fixed-point_logic>

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

<https://courses.cs.washington.edu/courses/cse344/13au/lectures/query-language-primer.pdf>
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

The lfp of lfp(FO) is kind of like the mu minimization operator. <https://en.wikipedia.org/wiki/%CE%9C_operator>

# Intuitionism / Constructive Math

Choice sequences

<https://en.wikipedia.org/wiki/Constructive_set_theory>

<https://en.wikipedia.org/wiki/Constructive_analysis>

# Proof Theory

See note n proof theory

# Recursion Theory

<https://en.wikipedia.org/wiki/Computability_theory>
<https://plato.stanford.edu/entries/recursive-functions/>
<https://mitpress.mit.edu/9780262680523/theory-of-recursive-functions-and-effective-computability/> Hartley Rogers

## Combinators

## Lambda Calculus

### Untyped

barendregt book
dana scot at lambda conf <https://www.youtube.com/watch?v=mBjhDyHFqJY&ab_channel=LambdaConf>
The lambda calculus as an unyped

[History of Lambda-calculus and Combinatory Logic Felice Cardone ∗ J. Roger Hindley †](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=959d32cfa6df9299312ba51e2102045e1f25bc18)

### Typed

See note on type theory

# Misc

<https://news.ycombinator.com/item?id=33236447>

[Book list](https://github.com/jaalonso/Libros_de_Logica/blob/main/README.org)

mathematical logic through python

[Mathematical Logic and Computation - Avigad](https://www.cambridge.org/core/books/mathematical-logic-and-computation/300504EAD8410522CE0C27595D2825A2)

[Handbook of mathemtical logic](http://www.alefenu.com/libri/handbooklogica.pdf)

<https://carnap.io/srv/doc/index.md>
forall x <https://www.fecundity.com/logic/>
jscoq, lean-web-editor, sasylf, pie
<https://github.com/RBornat/jape>

<https://home.sandiego.edu/~shulman/papers/induction.pdf>
equality as induction.
Defining the axioms of equality as an axiom schema.

<https://golem.ph.utexas.edu/category/2013/01/from_set_theory_to_type_theory.html> from set theory to type theory
ects - structural set theory. notion of set and function.

<https://golem.ph.utexas.edu/category/2012/12/rethinking_set_theory.html> rethinking set theory
