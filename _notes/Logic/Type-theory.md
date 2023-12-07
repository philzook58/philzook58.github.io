---
layout: post
title: Type Theory
---
- [What Are Types? What is Type Theory?](#what-are-types-what-is-type-theory)
- [Type Checking](#type-checking)
  - [Bidirectional Typing](#bidirectional-typing)
  - [Hindley Milner](#hindley-milner)
- [Systems](#systems)
  - [Typed Expressions](#typed-expressions)
  - [Simply Typed lambda Calculus (STLC)](#simply-typed-lambda-calculus-stlc)
  - [System T](#system-t)
  - [System F](#system-f)
  - [PTS](#pts)
    - [Lambda Cube](#lambda-cube)
  - [F Omega](#f-omega)
  - [CoC](#coc)
    - [CiC](#cic)
- [Martin Lof](#martin-lof)
  - [LF](#lf)
    - [Dedukti](#dedukti)
- [Subtyping](#subtyping)
- [Intersection Types](#intersection-types)
- [Recursive Types](#recursive-types)
- [Refinement Types](#refinement-types)
- [Quotient Types](#quotient-types)
- [Dependent Types](#dependent-types)
- [Two Level Type Theory](#two-level-type-theory)
- [Data Types](#data-types)
  - [Inductive Types](#inductive-types)
    - [Parameters vs indices](#parameters-vs-indices)
  - [Induction Recursion](#induction-recursion)
- [Syntax and Semantics](#syntax-and-semantics)
- [Judgement](#judgement)
- [Inference Rules](#inference-rules)
- [Computation Rules](#computation-rules)
  - [Conversion vs Reduction vs Expansion](#conversion-vs-reduction-vs-expansion)
- [Pattern Matching](#pattern-matching)
- [Metatheory](#metatheory)
  - [Mechanized Metatheory](#mechanized-metatheory)
  - [Decidability of type checking](#decidability-of-type-checking)
  - [Princiapl Types](#princiapl-types)
  - [Consistency](#consistency)
  - [Progress](#progress)
  - [Preservation, Subject Reduction](#preservation-subject-reduction)
  - [Normalization](#normalization)
  - [normalization by evaluation](#normalization-by-evaluation)
  - [Canonicity](#canonicity)
  - [Computation rules](#computation-rules-1)
    - [Completeness](#completeness)
    - [Soundness](#soundness)
    - [Head Normal Form](#head-normal-form)
    - [Value](#value)
      - [Neutral](#neutral)
      - [Canonical](#canonical)
    - [Reducible Expression](#reducible-expression)
    - [Curry vs Church style](#curry-vs-church-style)
    - [Large Elimination](#large-elimination)
    - [Excluded Middle](#excluded-middle)
    - [Sorts  \& Universes](#sorts---universes)
    - [Impredicative vs Predicative](#impredicative-vs-predicative)
    - [Proof Irrelevance](#proof-irrelevance)
    - [Inconsistent Combinations](#inconsistent-combinations)
    - [Extensionality](#extensionality)
- [Equality](#equality)
  - [Extensional vs Intensional](#extensional-vs-intensional)
  - [Observational Type Theory](#observational-type-theory)
  - [Judgemental/Definitional / Propositional](#judgementaldefinitional--propositional)
  - [Univalence](#univalence)
  - [HOTT](#hott)
    - [Older](#older)
- [Logical Relations](#logical-relations)
- [Realizability](#realizability)
- [Topics](#topics)
  - [Gradual Typing](#gradual-typing)
  - [Intersection types](#intersection-types-1)
  - [subtyping](#subtyping-1)
  - [union types](#union-types)
- [Bidirectional Typing Old](#bidirectional-typing-old)
- [Misc](#misc)
  - [Books](#books)

# What Are Types? What is Type Theory?

There isn't a good answer.

Type Theory is what a type theorist does. Useless answer but most honest. What is physics vs chemistry? There are things firmly in one subject (colliders, tylenol), but others in grey areas (nuclear, atomic spectra). Depends on what the person considers themselves, what journals they submit to.

Some goes for type theory. What is proof theory? Computer Science? Logic? It's somewhere in all of there.

 -[what is a type paulson](https://twitter.com/LawrPaulson/status/1521787594622783488?s=20&t=kBQ6NNrdoK-tcIkhvRqktQ)

- [What is a type](https://twitter.com/sliminality/status/1521546506452447233?s=20&t=kBQ6NNrdoK-tcIkhvRqktQ)

- "The question "What is a type?" has no useful answers. The correct question is "What is a type theory?" – and the answer is: it is a mathematical theory of a system of constructions. The types classify the  constructions supported by the theory." - Bauer

- [What We Talk About When We Talk About Types - Nick Benton](https://nickbenton.name/whatwetalkabout4web.pdf)
- [types are not sets - Morris classic](https://dl.acm.org/doi/pdf/10.1145/512927.512938)
- [What is a type on zulip](https://typ.zulipchat.com/#narrow/stream/279113-general/topic/What.20is.20a.20type.3F/near/230769268)

- [On the Relationship Between Static Analysis and Type Theory - Neel Krishnaswami](https://semantic-domain.blogspot.com/2019/08/on-relationship-between-static-analysis.html) "Anyway, my main thoughts on Li-Yao’s question are in a blog post I wrote a few years ago. Ravi Mangal wanted to know what the difference between static analysis and type theory were, and my answer was that you distinguish the two based on how sad you feel if you can’t prove a substitution theorem."

# Type Checking

<https://discuss.ocaml.org/t/writing-type-inference-algorithms-in-ocaml/8191>
[PL zoo](https://plzoo.andrej.com/)
[grow your own type system](https://github.com/tomprimozic/type-systems)
[inferno a library for unification in type systems](https://gitlab.inria.fr/fpottier/inferno) [hindley miler in applicative style](http://gallium.inria.fr/~fpottier/publis/fpottier-elaboration.pdf)
[How OCaml type checker works -- or what polymorphism and garbage collection have in common](https://okmij.org/ftp/ML/generalization.html)
[The Simple Essence of Algebraic Subtyping: Principal Type Inference with Subtyping Made Easy](https://infoscience.epfl.ch/record/278576)

## Bidirectional Typing

[Bidirectional Type Checking - jetbrains](https://www.youtube.com/watch?v=BL-OXeTtw1g&ab_channel=JetBrainsResearch)

mckinna mcbride gundry. tye inferencei n context
<https://adam.gundry.co.uk/pub/type-inference-in-context/#:~:text=We%20consider%20the%20problems%20of,for%20implementing%20type%20inference%20algorithms>.

Complete and easy Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism. Dunfield Krishnaswami
<https://arxiv.org/pdf/1306.6032.pdf>

FreezeML
<https://www.pure.ed.ac.uk/ws/portalfiles/portal/142279783/FreezeML_EMRICH_DOA21022020_AFV.pdf>

Nice simple tutorial
<http://davidchristiansen.dk/tutorials/bidirectional.pdf>

pfenning lecture notes
<https://www.cs.cmu.edu/~fp/courses/15312-f04/handouts/15-bidirectional.pdf>

## Hindley Milner

[wikipedia](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system)

<http://dev.stephendiehl.com/fun/006_hindley_milner.html>

[Hindley-Milner Elaboration in Applicative Style - Pottier](http://gallium.inria.fr/~fpottier/publis/fpottier-elaboration.pdf) <https://gitlab.inria.fr/fpottier/inferno>

type inference as generation and then solving of constraints

types are simple types + a var constructor
type schema are forall wrappers around a type
let allows you to generalize a type with vars into a schema.

<https://www.youtube.com/watch?v=NkAt9eApGSw&list=PLre5AT9JnKShBOPeuiD9b-I4XROIJhkIU&index=192&ab_channel=MichaelRyanClarkson>

env |- e : t -| C

take in env and e, output t and C. Set of contraints.
DCG might be nice for the constraints.

% type(+, +, - , -).
% constants
type(E, int(X), int, []).
type(E, bool(X), bool, []).
type(E, var(X), Y, []) :- lookup(X,E,Y).
type(E,ite(E1,E2,E3), tvar(T), C1 ++C2 ++ C3 ++ C) :-
  type(E, E1,T1,C1),  type(E, E2,T2,C2)

# Systems

<https://en.wikipedia.org/wiki/Lambda_cube> is a way to classify different subsystems

## Typed Expressions

Kind of it's nice to avoid all the lambda calculus stuff. Consider compound boolean and nat expressions.

```ocaml
#use "topfind";;
#require "ppx_jane";;
type ty = Bool | Nat
type term =
    True | False | If of term * term * term | Zero 
    | Succ of term | Pred of term | IsZero of term [@@deriving sexp, equal, compare]
let term_of_string s = Sexplib.Sexp.of_string s |> term_of_sexp
let ex = term_of_string "(if true true false)"
let () = Sexplib.Sexp.pp_hum Format.std_formatter (sexp_of_term ex)
```

```z3
;re
; very goofy since I have no evaluable forms
(declare-datatype Term
  ((True) (False) (Zero))
)

(declare-datatype Type
  ((Bool) (Nat))
)

(define-fun-rec hastype ((t Term) (ty Type)) Bool
  (match t (
    (True (= ty Bool))
    (False (= ty Bool))
    (Zero (= ty Nat))
  ))
)

(push)
(declare-const ty1 Type)
(assert (hastype True ty1))
(check-sat)
(get-model)
(pop)

(define-fun value ((x Term)) Bool
  true
)

(define-fun eval ((x Term) (y Term)) Bool
  false
)

(define-fun progress () Bool
  (forall ((x Term) (ty Type))
    (=> (hastype x ty)
        (or (exists ((y Term)) (eval x y))
            (value x))
    )))

(define-fun preservation () Bool
  (forall ((x Term) (y Term) (ty Type))
    (=> (and (hastype x ty) (eval x y))
        (hastype y ty)
    )))

(push)
(echo "progress")
(assert-not progress)
(check-sat)
(pop)

(push)
(echo "preservation")
(assert-not preservation)
(check-sat)
(pop)
```

Is normalization of typed expressions easy? We don't need logical relations?

## Simply Typed lambda Calculus (STLC)

typechecking stlc does not have the binding issues you might expect of a lambda calc

## System T

- [Harper Class notes](https://www.andrew.cmu.edu/course/15-312/recitations/rec3-notes.pdf)
- [Girard Proofs and Types](http://www.paultaylor.eu/stable/prot.pdf)
- <https://gregorulm.com/godels-system-t-in-agda/>
- [Avigad Feferman Dialectica](https://www.andrew.cmu.edu/user/avigad/Papers/dialect.pdf)

"Quantifier free theory of functionals of finite type"

## System F

<https://en.wikipedia.org/wiki/System_F>

polymorphic lambda calculus

Lambda2
Terms can depend on types. Big Lambda /\
(al types can dpeend on types)

[THE SYSTEM F OF VARIABLE TYPES, FIFTEEN YEARS LATER - Girard](https://core.ac.uk/download/pdf/82258639.pdf)
System F is developed on as a intuitionistic second order arithmetic like how system T is first order.

Data types are definable.
Strongly normalizaing

System F as dependent types. Type variables could be runtime data, just a special class of them. In that case, the polymorphic signature of a function is a dependent type.

Reynolds [towards a theory of type structure](https://www.cs.cmu.edu/afs/cs/user/jcr/ftp/theotypestr.pdf)
From the get go, considering the implementation of integers across two machines is brought up. A relational intepretation. The "inner" and "outer" view, one which sees representation and one that doesn't

[Types abstraction and parametric polymorphism](https://people.mpi-sws.org/~dreyer/tor/papers/reynolds.pdf)

Polymorphism is not set theoretic <https://inria.hal.science/inria-00076261/document>  <http://h2.jaguarpaw.co.uk/posts/polymorphism-is-not-set-theoretic/>

Uniform representation

[Polymorphism is set theoretic constructively - Pitts](https://link.springer.com/chapter/10.1007/3-540-18508-9_18)

[Theorems for Free - Wadler](https://people.mpi-sws.org/~dreyer/tor/papers/wadler.pdf)

```python
from typing import Tuple
def interp(typ):
  if typ == bool:
    {True, False}
  if typ == Tuple[A,B]:
    { (a,b)  for a in interp(A) for b in interp(B)}
  if typ == Callable[A,B]:


# we can't finitely list our universe. Since it needs to include all iterated arrow. Eh. I don't see why really.
Universe = {bool : {True, False}}
def Universe(S): # check if in universe
def Universe(S): # infinite stream.  
  yield {True, False}
  yield 
# Or maybe produce Z3 expressions. Hmmm.

Typ = Sort("Type")

def interp(ctx, ty):
  if ty == bool:
    ForAll([x,x1], interp(x,x1) == (x == x1))
  if ty == int:
  if ty == TVar:

  if ty == Tuple[a,b]:
  if ty == Callable[a,b]:
    ForAll([x,x1], interp(f,f1) == ForAll([x,x1], interp(x,x1) == interp(f(x), f1(x1))))
  if ty == Generic(X,T):
    ForAll([x,x1], )
  


# I can't enumerate ? forall X, 

```

## PTS

Pure Type Systems
Sorts, axioms

System U

### Lambda Cube

<https://cstheory.stackexchange.com/questions/36054/how-do-you-get-the-calculus-of-constructions-from-the-other-points-in-the-lambda/>

- stlc
- stlc+type operators. Lambdas at the type level. Does any term have type $\lambda x. x -> x$? I don't think so. Could add constants like `List` but again, no term has this type.
- system F. $\lambda 2$ Adds Big Lambda at at term and forall at type level. Polymorphic types. $\forall x. x -> x$
- $F\omega$ $\lambda \omega$
- $lambda P$

Other interesting named systems don't fit in the cube though.

"computational strength" LF has same computayional strength as stlc. what does that mean?

## F Omega

first class type constructors.

## CoC

Calculus of constructions

Equi vs iso recursive types

[Strong Normalization for the Calculus of constructions - Casinghino](https://docslib.org/doc/4739017/strong-normalization-for-the-calculus-of-constructions)

### CiC

Whole different ball game (?)
[Luo's thesis - An Extended Calculus of Constructions](https://era.ed.ac.uk/bitstream/handle/1842/12487/Luo1990.Pdf)
[Proof on normalization of CIC and its consistency](https://coq.discourse.group/t/proof-on-normalization-of-cic-and-its-consistency/444)

# Martin Lof

A distinctin can be drawn

## LF

$\lambda P$
$\lambda \Pi$
<http://www.cs.cmu.edu/~aldrich/sasylf/>
Twelf <http://twelf.org/wiki/Main_Page> <https://www.cs.cmu.edu/~fp/papers/cade99.pdf>

Abella
Beluga

There is a claim that LF (which is a corner of the lambda cube?) has enough power to do lots of good stuff for progamming language metahtoery bu not so much that your life sucks.
[A Framework for Defining Logics harper honsell plotkin 93](https://homepages.inf.ed.ac.uk/gdp/publications/Framework_Def_Log.pdf)
judgements as types

<https://en.wikipedia.org/wiki/Logical_framework> logical framework can refer to a general notion of a system you encode your logic into or a specific type theory
lambda pi system <https://en.wikipedia.org/wiki/Dependent_type#First_order_dependent_type_theory>

LFSC
smtlib3 is also an LF?

### Dedukti

dedukti - see term rewriting

<https://arxiv.org/abs/2311.07185>  Dedukti: a Logical Framework based on the λΠ-Calculus Modulo Theory
<https://deducteam.github.io/>
<https://github.com/Deducteam/lambdapi> is the assistant? VS code extension

```bash
echo "
(; https://deducteam.github.io/tutorial.html 
Doesn't seem valid
#NAME foo.

;)

(; declaring new types. 'static' ;)
A  : Type.
Nat: Type.
Z  : Nat.
S  : Nat -> Nat.

(; def and just stating existence are different
Notice the defnition of plus is open.
;)
def 1 := S Z.
def 2 := S 1.

def plus: Nat -> Nat -> Nat.
[m]   plus  Z    m --> m
[n,m] plus (S n) m --> S (plus n m).

(; also fine? superfluous thugh. ;)
[n,m] plus n (S m) --> S (plus n m).


Bool : Type.
true : Bool.
false : Bool.

def equal : Nat -> Nat -> Bool.
[] equal Z Z --> true
[n,m] equal (S n) (S m) --> equal n m
[] equal (S _) Z --> false
[]  equal Z (S _) --> false.
(; avoiding intermediate periods makes it kind of a block of declarations.  ;)


IsTrue : Bool -> Type.
tt : IsTrue true.

#CHECK tt : IsTrue (equal Z 1).
#ASSERT tt : IsTrue (equal Z Z).
#EVAL (equal Z Z).

def test1 : IsTrue (equal (plus 1 1) 2) := tt.

(; partial functions are fine? They just get stuck. ;)
def pred : Nat -> Nat.
[ n : Nat ] pred (S n) --> n.

Listn : Nat -> Type.
nil   : Listn Z.
cons  : n: Nat -> A -> Listn n -> Listn (S n).

(; Hmm. but.. I need to take in n?
def length : n : Nat -> Listn n -> Nat.
[] length _ nil --> Z.
[n] length _ (cons _ _ tl) --> length tl 
;)

(; smart constructors. Huh. So because there is a normalizaton, we're chill.
   WHat makes this a 'constructor'. Nothing really.
;)
Int : Type.
def Diff : Nat -> Nat -> Int.
[m,n] Diff (S m) (S n) --> Diff m n.

def abs : Int -> Nat.
[n] abs (Diff Z n) --> n.
[n] abs (Diff n Z) --> n.

def append: n: Nat -> Listn n -> m: Nat -> Listn m -> Listn (plus n m).
[l2] append _ nil _ l2 --> l2
[n,l1,m,l2,a]
  append _ (cons n a l1) m l2 --> cons (plus n m) a (append n l1 m l2).

#INFER nil.
#PRINT \"hello world\".
(;  partial equality. Neeeeeat. ;)
def A_eq : A -> A -> Bool.
[a] A_eq a a --> true.  

  
  (; Thi _does_ extend the power of equal, because stuck terms are also equal now. like pred Z ;)
[ n : Nat ] equal n n --> true.
  " > /tmp/append.dk
dk check  /tmp/append.dk #-v 
```

confluence checking. It tries to? Or maybe lambdapi does? "Correct by cnfluence"  `dk check --confluence=CMD`
add new rules, confluence checking demonstrates that the new rules are "consistent" wth the old one?
<https://termination-portal.org/wiki/TPDB> needs to support tpdb format. <http://cl-informatik.uibk.ac.at/software/csi/ho/>
<http://cops.uibk.ac.at/?q=hrs> confluence problem database

`dk meta` rewrites a dedukti file. Could I write an egraph as a file and then rewrite it?

<https://github.com/Deducteam/Dedukti/tree/master/examples> examples

<https://github.com/Deducteam/Dedukti/blob/master/README.md> manual

```
#CHECK t1 == t2.
#CHECKNOT t1 == t2.
#EVAL[10]
#EVAL[SNF]
```

commands beautify, check, dep, meta, top a toplevel, prune

kontroli is rust version <https://arxiv.org/pdf/2102.08766.pdf> Safe, Fast, Concurrent Proof Checking for the
lambda-Pi Calculus Modulo Rewriting

# Subtyping

Supposedly is kind of a shit show.

# Intersection Types

<https://cs.stackexchange.com/questions/162744/what-is-practically-preventing-us-from-applying-set-theoretic-types-in-engineeri?stw=2>

# Recursive Types

iso recursive vs. equirecursive

# Refinement Types

[Refinement Types: A tutorial](https://arxiv.org/abs/2010.07763)
[Explicit Refinment Types](https://dl.acm.org/doi/10.1145/3607837)
"Instrinsic semantics niterprets typing relationd rathert than terms

- FStar
- Liquid Haskell

- PVS?

```prolog
:- initialization(main,main).
:- op(900, xfx, user:(::)).
tt :: unit.


main(_) :- tt :: Ty, writeln(Ty). 
```

```z3

```

# Quotient Types

Cody has alluded to there being accidental stumbling blocks into inconsistency here

# Dependent Types

See also

- Coq
- lean

Sometimes we get hung up on that types in some systems are compile time (static) and values are run-time (dynamic).
Certainly dynamic typed languages put the types at runtime. Some statically typed languages persist the type information somewhere at runtime so you can reflect to it if need be,
It is a little more subtle that you can pull values back into compile time. Really, programs themselves are compile time things that are talking about abstract runtime values. The variable `x` is kind-of sort-of a value (I am using terminology in a highly loose non-technical colloquial sense here).

Dependent types let you mention abstract runtime variables and concrete values in the types. It's sort of a natural box in the compile-runtime, type-value grid.

calculus of constructions

- <http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/>
- [a tutorial implementation of dependtly typed lambda calc](https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf ) <http://lambda-the-ultimate.org/node/2340> discussion Simply Easy
- <http://augustss.blogspot.com/2007/10/simpler-easier-in-recent-paper-simply.html>
- <https://eb.host.cs.st-andrews.ac.uk/writings/thesis.pdf> - Brady thesis
- <https://asset-pdf.scinapse.io/prod/2145108549/2145108549.pdf> - idris design and implementation
- [mini-tt](http://www.cse.chalmers.se/~bengt/papers/GKminiTT.pdf)
- Weirich OPLSS 2013
- [easy as pie](https://www.seas.upenn.edu/~sweirich/papers/tfp07.pdf)
- [elaboration zoo](https://github.com/AndrasKovacs/elaboration-zoo)

# Two Level Type Theory

[two level type theory staging](https://andraskovacs.github.io/pdfs/2ltt.pdf)

[peridot](https://news.ycombinator.com/item?id=31325581)

# Data Types

What makes "datatypes" different from the things above? They aren't. My organization is all fucked.

Schema for allowable definitions.

Introduction
Elimination
Computation Rule

## Inductive Types

[nlab](https://ncatlab.org/nlab/show/inductive+type)
<https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html>

Curious restrictions on their form.
positivity restrictions

### Parameters vs indices

<https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html#axiomatic-details>

parameters stay fixed / opaque in all definitions.
 indices can be

```coq
Inductive Vec a : nat -> Type :=
 | VNil : Vec a 0
 | VCons : forall n, a -> Vec a n -> Vec a (S n)
. 
```

 n is index. a is argument

Equi vs Iso recursive types - <https://www.cs.cornell.edu/courses/cs4110/2012fa/lectures/lecture27.pdf> Does equality hold on the nose in recursion (equi) or is there some unpacking to do (iso)
Coinductive Types

## Induction Recursion

<https://ncatlab.org/nlab/show/inductive-recursive+type>
[induction recursion](https://en.wikipedia.org/wiki/Induction-recursion)
[induction induction](https://en.wikipedia.org/wiki/Induction-induction)

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

# Pattern Matching

There is a choice whether to consider pattern matching primitive or not
Eliminators
dependent pattern matching

Conor Mcbride thesis

[a few constructions on constructors](http://www.cs.ru.nl/~james/RESEARCH/types2004.pdf)
[Pattern Matching Without K](https://jesper.sikanda.be/files/pattern-matching-without-K.pdf)

# Metatheory

Many type systems talk about lambda calculus, so the metatheory is intertwined with the rewrite theory of lambda calc.

### Mechanized Metatheory

### Decidability of type checking

type checking is the question of whether given all the pieces going into the judgement under line of the inference rule, is it decidable to construct a typing tree that produces such a thing. Even this seemingly simple question can be undecidable in some type systems, because higher up in the typing tree you may ask questions that are very difficult. In the presence of nontermination, you probably are encountering a variant of the halting problem. Undecidability of type checking is typically considered to be an undesriable property, but people are willing to entertain the notion.

### Princiapl Types

Type inference supposes I give the context and term, but leave out the type, can I construct both the typing tree and the type. [Principle types](https://en.wikipedia.org/wiki/Principal_type) are asking whether there is a unique most general type that can be inferred.

[What are principal typings and what are they good for?](https://dspace.mit.edu/bitstream/handle/1721.1/149247/MIT-LCS-TM-532.pdf?sequence=1&isAllowed=y)

"Uniqueness of types" may hold in some system.

### Consistency

### Progress

Well typed terms can take a step under the eval relation or are values.

A kind of liveness property? Eh. Really it feels kind of "coinductive" to me.

### Preservation, Subject Reduction

under evaluation, terms remain well typed.

This can mean evaluation does not cause types to change. These are slightly different statements that may not be equivalent in all systems

Preservation is very reminiscent of verifying that types are an invariant, or that the typing relation is an invariant set.

### Normalization

<https://www.pls-lab.org/en/Normalization>

### normalization by evaluation

```ocaml

type term = Lam of string * term
 | Var of string
 | App of term * term

type typ = Arr of typ * typ
  | Unit

type value = Arr of value Value.Map.t | UnitV

let eval : term -> typ -> value

```

### Canonicity

The same thing as normalization?
<https://cs.stackexchange.com/questions/112893/what-does-canonicity-property-mean-in-type-theory>

## Computation rules

### Completeness

### Soundness

Soundness is whatever the type system claims to show about evaluation, it shows. Sometimes this is progress + preservation

### Head Normal Form

### Value

<https://ice1000.org/2019/04-07-Reduction.html>

What are possible definitions of "value"?

- a subset of terms
- a separate entity akin to terms
- semantic objects

Some of the distinction and confusion depends on how much you rely on your host meta system.

#### Neutral

#### Canonical

### Reducible Expression

### Curry vs Church style

Extrinsic vs Instrinsic types

### Large Elimination

pattern matching on a value to construct a value of Type
<https://cstheory.stackexchange.com/questions/40339/what-exactly-is-large-elimination>

```coq
bool_to_type : bool -> Type := fun b =>
     match b with
         | true => Unit
         | false => Empty
```

[impredicative polymorphism  + exlcuded middle + large elimination can only choose 2](https://github.com/FStarLang/FStar/issues/360)

### Excluded Middle

```coq
Axiom classic : forall P:Prop, P \/ ~ P.
```

### Sorts  & Universes

<https://coq.inria.fr/refman/language/core/sorts.html>

- Prop vs Type vs Set - Prop is impredicative. Prop and Set are deleted during extraction? Which make them interestingly different from a metaprogramming perspective.

`Prop` `SProp` `Set`
`SProp` is Prop with proof irrelevance

Prop is erased at extraction.
Prop doesn't have large elimination. But it is impredicative and can support excluded middle.

```coq
Inductive Bool : Prop := T : Bool | F : Bool.

Definition two_elements_Bool (H : T = F) : False :=
  match H in (_ = y0) return (match y0 with
                                | T => True
                                | F => False
                              end) with
    | eq_refl => I
  end.
(* Error: *)
(* Incorrect elimination of "y0" in the inductive type "Bool": *)
(* the return type has sort "Type" while it should be "Prop". *)
(* Elimination of an inductive object of sort Prop *)
(* is not allowed on a predicate in sort Type *)
(* because proofs can be eliminated only to build proofs. *)
```

[why does coq have prop(https://cstheory.stackexchange.com/questions/21836/why-does-coq-have-prop)]

Is there a difference between Sorts and Universes?
<https://github.com/jdolson/hott-notes/blob/pdfs/pdfs/notes_week5.pdf>
Universes are

Algerbaic universes - If the levels of type are a DAG, they can be ordered. So one doesn't eagerly pick integer levels for Type. Instead you maintain contraints like max{l1,l2} etc.

### Impredicative vs Predicative

This is describing allowing some kind of form of self reference I think.

Impredicative types allow quantification over themselves.
Prop

### Proof Irrelevance

Propositional extensionality implies proof irrelevance
<https://coq.inria.fr/library/Coq.Logic.ProofIrrelevance.html>
Axiom proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.

<https://github.com/coq/ceps/pull/32> RFC: Disentangling erasure and proof irrelevance

It feels like proof irrelevance and erasure are related concepts, but like almost everything in type theory there is probably a time and place and level of sophistication to consider them as distinct

[Irrelevance, Polymorphism, and Erasure in Type Theory](https://pdxscholar.library.pdx.edu/open_access_etds/2674/)

[Berardi's paradox which says that in the calculus of constructions, excluded middle (EM) and axiom of choice (AC) imply proof irrelevance (PI).](https://coq.inria.fr/library/Coq.Logic.Berardi.html)

### Inconsistent Combinations

See counterexamples in type theory

- Berardi's paradox above
- Markov + ? <https://ncatlab.org/nlab/show/Markov%27s+principle> <https://en.wikipedia.org/wiki/Markov%27s_principle>

### Extensionality

Extensionality is a notion that applies to more than just function and equality types.
<https://cstheory.stackexchange.com/questions/17636/%CE%B7-conversion-vs-extensionality-in-extensions-of-lambda-calculus>

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

# Equality

[carette definitional equality](https://twitter.com/jjcarett2/status/1522973680241946625?s=20&t=kBQ6NNrdoK-tcIkhvRqktQ)

### Extensional vs Intensional

Extensional equality collapses definitional and propositional equality.

Adding a rule

```
Gamma |- t : Id_Type A B
------------------------
Gamma |- A = B
```

Notice that this is a transition from a typing judgement to a definitional equality judgement. Very different fellas.

### Observational Type Theory

[observational type theory](http://www.strictlypositive.org/ott.pdf) type theory has an equality type and refl. Extentional type theoru adds reflection, intentional adds eliminators

[pavel summarizing some different choices](https://pavpanchekha.com/blog/itt-equality.html)

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

### Univalence

Implies extensionality
Example `unit' = unit`
Isomorphisms

## HOTT

The homotopy type theory book

- [Escardo notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/)
- [The HoTT game](https://thehottgameguide.readthedocs.io/en/latest/getting-started/index.html)
- [Introduction to Cubical Type Theory (Part I) youtube](https://www.youtube.com/watch?v=6cLUwAiQU6Q&ab_channel=Favonia)
- [CSCI 8980 Higher-Dimensional Type Theory](https://favonia.org/courses/hdtt2020/)

- [cubical paper](https://arxiv.org/pdf/1611.02108.pdf)

Implementing Patch Theories in Homotopy Type Theory <https://www.cs.ru.nl/bachelors-theses/2023/Dick_Blankvoort___1056960___Implementing_Patch_Theories_in_Homotopy_Type_Theory.pdf>

<https://www.youtube.com/watch?v=Pu16iodESTU&list=PL245PKGUDdcN9-El9D7DRefwX4c9feiYq&t=594s&ab_channel=JacobNeumann>
Youtube videos

### Older

2018

<https://epit2020cnrs.inria.fr/> spring school
Type/Space        A type
Elekemntn/Point   t:A
type and point may depend on other points
x:A1, x2:A2 |-  B(x1,,x2) type

R^n depends on n. n : N |- R^n type
[a,b] depends on a,b, and a <= b
a:R, b:R, p :(a<= b) |- [a,b]
Equality judgemental equal
A === B equal types
s ===_A t  equal points

Type theory as formal system
Gam |- A type
t A
A === B
s ===_A t

rules of inference

Base space A
a:A |- B(x)
fiber at x.
ttoal space - dpeendent sum

Basic constructions

dependent sum

<https://fplab.wordpress.com/2015/05/09/hott-for-lazy-functional-programmers/>

The most straightforward computational attack on homotopy is usuing a trinagulated mesh that I think is fairly intuitive to computer people

Computerizing something involes:

- how to you even represent the thing you want to talk about
- howw do you actually compute answers to interesting questions. I divide these into differewnt classes 1. Just recognize something, i.e.e proof checking or 2. Calculate or find something, i.e. actual numerical computations or proof finding or what have you. 1. Is often an interesting thing to start with since it is easier even if what you really want is 2.

Paths are lists of adjacent vertices.

Using haskell gadts for example, we can encode all the paths and then use the types to enforce that the path is actually connected.

Another persepctive on this is to encopde the proerties of the mesh in logic, like first order logic.
Z3 is a way to make this conrete

From the perspective of systems like Coq or agda, these two pictures become the same thing. There systems have the notion of inductive predicates that boil down to defining a datatype like that in Haskell.

It sucks to work with this stuff though.

A second straightforward attack to model homotopy would be to directly model functions from the interval
R -> R.
Reals are floats.

We might try to directly model these things in functions and use functional programming
def homo1():

```python
def composepath(p1,p2):
  assert(p1(1) == p2(0) )
  def res(t):
    if t < 0.5:
      return p1(2 * t)
    else:
      return p2(2*t-1)
  return res
```

Skeletonizing this path with an open cover.
1 open cover = [0,1) and (0,1]

Or we might try to take a more symbolic approach, like using sympy or some custom dsl.
The difference here is tha6t in many languages, lambdas are basically totally opaque. There are advantages and disadvenmtages to
this rule. It does not have to be so. Languages with strong metaprogramming paradigms
(and I include lisps, Julia, and coq here) let you poke around in the guts to varying degrees.

Reals as floats may be objectionable to your sensibiliuties. Then perhaps a preferable approach may be to use exact reals, numbers that retain the capacity to be computed to arbitrary precision upon request.

Maybe there is more connection to my path thing than I realezied

Higher inductive types are where it is actually at I guess.

<https://www.youtube.com/watch?v=A6hXn6QCu0k> emily reihl - inifnity categroeis for undergrads, but really it's about homotopy type thoery

11/2020
<https://github.com/HoTT-Intro/Agda>
I screwed up my emacs agda by having a rotten tuareg in it. I think
<https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes>

<https://pure.itu.dk/portal/files/84649948/icfp19main_p164_p.pdf> - ICFP cubical agda, a depdently typed programming language with higher inductive types. Interestingly, from Mertberg's demo, I feel like the emphasis was not on cubical itself. More interested in standard HoTT they just want it to be better

HoTT - quotients supposedly? Fractions? Integers vs naturals. I guess that's the zeroth.
Or maybe True / False modulo True = False?
Anders Morberg - cubical agda  <https://vimeo.com/459020971>

```agda
data _===_ {A : Set} (x : A) : A -> Set where
  refl : x == x

funExt

replcace inductive === with paths

{-# OPTIONS -- cubical #-}
open import Cubival.Foundations.Prelude
                        Equiv
                         Isomorphism
                         Univalence
                         Cubical.Data.Int
                         Cubical.Data.prod

-- I , npoitns i0, i1
apply0 : (A; Type ) -> (p : I -> A) -> A
apply0 A p = p i0

refl' : {A : Type} (x : A) -> x \== x -- PathP (\ _ -> A) x x
refl' x = \i -> x

-- x \== x  h means PathP (\ _ -> A) x y
-- path over path. depednent paths

cong' : {A B : Type} (f : A -> B) {x y : A} -> x == y -> f x == f y
cong' f p = \ i -> f ( p i )

funext'  : {A B : Type} (f g : A -> B) {x y : A} -> ( p: x : A ->  f x == g y ) -> f == g
funext p i = \x -> p x i

transport' : {A B : Type} -> A == B -> A -> B
trasnport' p x = transp (\i -> p i) i0 x

-- another primitive called hcomp

ua' :  {A B : Type} -> A ~ B -> A == B
ua' e = ua e

isToEquiv' : {A B :type} -> Iso A B -> A ~ B
isToEquiv' e =  isoToEquiv e

isoToPath : Iso A B -> A == B
isoToPath e = ua (isoToEquiv e)

data Bool : Type where
   false : Bool
   true : Bool

not : Bool -> Bool
not false = true
not true = false

notPath : Bool === Bool
notPath = isoToPath' (iso  not not rem rem)
  where
  rem : (x : Bool) -> not (not x) == x
  rem false = refl
  rem true = refl

transport notPath true -- false

sucPath : Int === Int
sucPath = (isoToPath' (iso sucInt predInt sucPred redSuc)

transport ( sucPath . sucPath) (pos 4)

-- multisets

data FMSet (A : Type) : Type where
   [] : FMSet A
   _::_ : A -> FMSet A -> FMSet A
   comm : ( x y : A) (xs : FMSet A) ->
         x :: y :: xs == y :: x :: xs
    trunc : isSet (FMSet A) -- UIP

_++_ : {A : Type} -> FMSet A -> FMSet A -> FMSet A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)
(comm x y xs i) ++ ys = comm x y (xs ++ ys) i

-- can prove all kinds of things : xs ++ [] == xs ...

Cubical.HITs.FiniteMultiSet

unitr-++ : {A : Type} (xs : FMSet) -> xs ++ [] == xs
unitr++ [] = refl
unitr++ (x :: xs) =

SIP structure idenity principle
Cubical.Algerba.Monoid.Base -- reflection
```

queues, matrices. Huh. representiation independence transportiung proofs.

<https://arxiv.org/abs/1701.04391> - de moura selsam. good explanation of equality type
John Major equality - conor mcbride
Doing raw recursor proofs. Can I do it? I feel like it's kind of straightforward.
Begin able to write out exactly where I want the equality applied via a lambda.
Could Axiomatize equality rather than use Inductive definition.
The pattern match of a HIT must desguar into recursors?

Types are spaces.
values are points
dependent types are fibrations
identity types are paths

Other weirdness:
Observational type theory

Describing a concrete simplex as a gadt.
How do you make a correct by construction data structure of a path?
A list of vertices. Fine. But is there a path between each of them?
Ok, list of edges. Do those edges meet?

9/2018

univalence let's you turn isomorphisms into equality and get isomorphisms out of equalities.

HIT - Higher inductive types. Instead of always needing the data constructor to end with the type itself A , now it can end with =_A also. You can do this using

recursors. Patrern matching is cool,. but it can be desgared into something else. A function that takes a continuation for each case of the type.

focus on inclusion and projection maps of the basic simplex

Cubical Sets.

of of the basic interval.

Simpilical Sets.

By using the basic simplex with its inclusion maps as sort of a index into your complex, you can grab all n-simplices at once. This is a Functor relation.

$latex

Great intro

<https://arxiv.org/pdf/0809.4221>

You can use a postulate methodology where you slam out all the pieces of your type as axioms

Dan Licata explaining how to use hiding to implement HIT. You export an interface. This let's you postulate less

<https://homotopytypetheory.org/2011/04/23/running-circles-around-in-your-proof-assistant/>

Homotopy group of circle is Z

<https://homotopytypetheory.org/2012/06/07/a-simpler-proof-that-%CF%80%E2%82%81s%C2%B9-is-z/>

<https://www.cs.cmu.edu/~drl/pubs/ls13pi1s1/ls13pi1s1.pdf>

You always need streicher K and rewriting turned on. What do these do?

<https://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/>

<https://stackoverflow.com/questions/39239363/what-is-axiom-k/39256457>

Axiom K is Uniqeness of Identity Proofs. Default pattern matching allows this. Modified pattern matching doesn't. The recursor form doesn't seem to have this problem

```agda
    uip : {A : Set} -> {a : A} -> (p q : a ≡ a) -> p ≡ q
    uip refl refl = refl
```

<https://github.com/HoTT/HoTT-Agda>

Kind of hard to navigate. Like the std-lib but harder.

Useful start in core. Check out univalence, check out the types folder. Look at the normal types like Bool, Nat, List. Now check out Circle, Torus,

Interesting lectures using cubicaltt

<https://github.com/mortberg/cubicaltt/tree/master/lectures>

# Logical Relations

- [History of programming course](https://felleisen.org/matthias/7480-s21/22.pdf) <https://felleisen.org/matthias/7480-s21/lectures.html> Mentions Amal thesis as being good
- [Intro to logical relations](https://www.cs.uoregon.edu/research/summerschool/summer16/notes/AhmedLR.pdf)

Tait proved strong normalization using them 1967.

Parametricity is supposedly an example also

Chapter (crary) in Advanced Topics in Types  by Pierce
People keep referencing Mitchell 1996

Logical relations as a generalization of homomorphism - Stump podcast referencing a paper

# Realizability

[andrej notes on realizability](https://github.com/andrejbauer/notes-on-realizability)

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

# Topics

[A collection of programming languages and type systems.](https://github.com/ayazhafiz/plts)

## Gradual Typing

## Intersection types

## subtyping

ALgebraic subtyping
<https://lptk.github.io/programming/2020/03/26/demystifying-mlsub.html>
mlsub
dolan thesis

## union types

# Bidirectional Typing Old

Notes on Bidirectional Typing and the Meaning of Horizontal Lines

```ocaml
type var = string
type typ = Unit | Arr of typ * typ
type expr = Var of var | Lam of var * expr |
     App of (expr * expr) | TT | Annot of (expr * typ)
type typ_ctx = (var * typ) list

let rec type_check gamma e t = match e,t with
  (* | Var v, t -> (List.assoc v gamma) = t *)
  | TT , Unit -> true
  | Lam(x,e), Arr(a1,a2) -> type_check ((x,a1) :: gamma) e a2
  | _,  _  -> let t' = type_infer gamma e in
              t = t'
and type_infer gamma e = match e with
  | Var v -> List.assoc v gamma
  | Annot(e, t) -> let c = type_check gamma e t in
                  if c then t else failwith "Bad annotation"
  | App(f, x) -> let Arr (a,b) = type_infer gamma f in
                let c = type_check gamma x a in
                if c then b else failwith "App typecheck failed"
  | _ -> failwith "can't infer"

(* #use bidi.ml;;
type_check [] TT Unit;;
type_infer [] (Annot (Lam ("x", App(Var "x", TT)), Arr(Arr(Unit,Unit),Unit)));;
type_infer [] (Annot (Lam ("x", TT), Arr(Unit,Unit)));;
*)


```

```prolog

% It works but it is not well moded

type(G, var(X), A) :- member( X - A  , G ). % member is a little wrong.
type(G, ann( E, T), T) :- type(G, ann(E,T), T).
type(G, tt, unit).
type(G, lam(X,E), arr(A1,A2)) :- type([X - A1 | G], E, A2 ).
type(G, app(E1,E2), B) :- type(G, E1, arr(A,B)), type(G, E2, A).

%?- type([], lam(x,lam(y,var(y))), T).
%T = arr(_6662, arr(_6680, _6680)) 
```

```coq

Require Import String.
Inductive type :=
    | unit
    | arr : type -> type -> type
    .
Inductive expr :=
    | var : string -> expr
    | lam : string -> expr -> expr
    | ap : expr -> expr -> expr
    | tt : expr
    | ann : expr -> type -> expr.

Fixpoint type_eq a b :=
     match a,b with
     | unit, unit => true
     | (arr x y), (arr z w) => andb (type_eq x z) ( type_eq y w)
     | _, _ => false
     end.

Definition ctx := list (string * type).
Require Import List.
Import ListNotations.

Search app.

Fixpoint lookup k l := match l with 
| (t,v) :: ls => if String.eqb k t then v else lookup k ls 
| [] => unit (* chris mocked me for this *)
end.
(** adequacy *)
Inductive hastype (gamma : ctx) : expr -> type -> Type :=
   | Var : forall x A, lookup x gamma = A -> hastype gamma (var x) A
   | UnitI : hastype gamma tt unit
   | ArrI :  forall e x A1 A2, hastype ((x, A1) :: gamma) e A2 -> 
             hastype gamma (lam x e) (arr A1 A2)
   | ArrE :  forall A B e2 e1, 
             hastype gamma e1 (arr A B) ->
             hastype gamma e2 A ->
             hastype gamma (ap e1 e2) B
    | Anno : forall a b e, 
        hastype gamma e a -> 
        type_eq a b = true -> 
        hastype gamma (ann e a) b
           .

Inductive inferstype (g : ctx) : expr -> type -> Type :=
| Varinf : forall x A, lookup x g = A -> inferstype g (var x) A
| ArrEInf :  forall A B e2 e1, 
            inferstype g e1 (arr A B) ->
            checkstype g e2 A ->
            inferstype g (ap e1 e2) B
| AnoInf : forall a e, checkstype g e a -> 
           inferstype g (ann e a) a

with checkstype (g : ctx) : expr -> type -> Type :=
| UnitIc : checkstype g tt unit
| ArrIc :  forall e x A1 A2, checkstype ((x, A1) :: g) e A2 -> 
          checkstype g (lam x e) (arr A1 A2)
| Subc : forall A e B, inferstype g e A -> type_eq A B = true -> checkstype g e B
.

Goal checkstype [] tt unit. eauto using checkstype. Qed.
Goal hastype [] tt unit. eauto using hastype. Qed.
Goal {t & hastype [] tt t}. eauto using hastype. Qed.
Goal checkstype [] (lam "x" tt) (arr unit unit).
eauto using checkstype. Qed.
Goal hastype [] (lam "x" tt) (arr unit unit).
eauto using hastype. Qed.
Goal hastype [] (ap (lam "x" tt) tt) unit.
eauto using hastype. Qed.
Goal inferstype [] (ap 
                   (lam "x" tt)
                   tt) unit.
                   eauto using inferstype, checkstype. Abort.

Goal inferstype [] (ap 
                   (ann (lam "x" tt) (arr unit unit)) 
                   tt) unit.
                   eauto using inferstype, checkstype. Qed.
(* eapply ArrEInf. 
- eapply AnoInf.
apply ArrIc. apply UnitIc.
- apply UnitIc.
Qed. *)  




(* Decision procedures. 

Fixpoint inferstype (g:ctx) (e : expr) : option {t : type | inferstype g e t} :=
Fixpoint checkstype (g:ctx) (e : expr) (t : type) : option (checkstype g e t) :=

sound : checkstype -> hastype
complete : hastype -> checkstype \/ inferstype
*)

From elpi Require Import elpi.






```

I picked bidirectional typechecking for reading group this week. A lovely survey paper.

Bidirectional typing is a methodology for taking piles of typing rules and making them more algorithmic.
This gets into my strike zone, as an outsider to type theory and logic, the notion of inference rules bends me in knots. I don't know what they mean. I do have some notion of computer programs having meaning. C, python, C++, ocaml, even Coq mean something to me because they create artifacts that exist and live outside of myself. They run. Their execution becomes fact regardless if I understand them or not. Executable programs become a part of the physical world.
I do not feel the same about mathematics or computer science written down in papers. It is static and only moves in the minds of people. I do not feel compelled to consider what is written in a paper as fact, a fait accompli, if I do not personally understand it. I don't think many people are trying to willfully deceive me in the academic literature, but there is always the possibility and that of self deception.

So for me, a pile of cryptic symbols with horizontal lines is unacceptable and contains almost no meaning. It begins to have meaning when I know how to translate the concepts into an executable programming language.

These concepts also being to have meaning if I personally know how to manipulate them with paper and pencil.

To put symbolic mathematical stuff in a computer, a standard methodology is to consider expressions as trees. We then want to manipulate those trees in programs or produce new trees.

Something that gives me conniptions is that implication $$\rimpl$$, turnstile $\vdash$, And horizontal bars are all some kind of notion of logic implication, albeit with the subtlest conceptual and mechanical distinctions. Somehow it the interplay of pushing things around between these three similar things encapsulates a notion of logical deduction. Super bizarre.

B is mangetic field, Gamma is a context

What are types?

Checking is easy?
Inference is hard?

Is this always true?
Checking of application is hard
f x : b  because it needs to invent an inner type.

We can make checking always go through with intense annotations.

infertype below the line is good. It is producing information
infertype above the line is bad. It needs a information producing process to output

It almost feels like a constraint satisfaction problem to me.
Perhaps the more flexible notion of a prolog search with pruning.

We want to pick an ordering and infer/check for the rules such that
they are well moded.
We want as many infers below lines and checks above lines as possible. These may be weighted by some notion of painfulness of annotation. Freqeuncy of usage * annotation size perhaps.
To require a synethsizing derivation is bad. To produce a synthesizing derivation is good.

The Pfenning recipe is a heuristic

Well moded : premise known.

The rules aren't independent of each other though? How does that hjapen?
Yes. The rules need to match up to each other.
Maybe really the cost is every annotation. which happens when there is a form that infers up top but checks below the line.

Of course, a language designer is not constrained to a fixed system. Adding extra forms,, or interesintg new
contexts or ways of thinkgin about things.

elimination forms are often in inference because there is an invented type

type-directed synthesis of programs is proof search.

1. principal judgement
2. elimination synethesize, introduction check. Elimination is usually above and introuducion usually below.
  This is counterintuitive, we have to step backward to step forward. WWe don't want synthesis above and check below.

A pile of introductions should just check? Carry the top level information through

subtyping :< often has input mode. It's easy to tell if things are subtypes than to come up with a maximal type persay

We don't want to dump information

The simply typed lambda calculus is kind of a bad example. It is so simple that really the nonbidirectional version does a pretty dang good job in raw prolog.

Inference rules: What is their computational reading/encoding?
The notation is extremely vague if this is your desire.

1. The expression below the line defines a relation.

Relations may be represented different ways
R a b c
Am I mixing types and expressions

1. [(a, b, c)] - explicit list (possibly infinite)
2. a -> b -> c -> bool  (decidable or partial depending on language) indicator function
3. Halfsies. a -> [(b,c)], a -> b -> [c],  in this sense a -> b -> c -> bool is really a -> b -> c -> [()]
3. type Rel a b c = a -> b -> c -> Prop -- a formula
5. explicit data type. data Rel = | True | False | And (Rel) (Rel) | Or |
4. R(A,B,C). -- prolog
5. C C++, Java, Python? Do they give any new ideas?

Ok but what about *Rules*. Different but related question.

1. Prolog clause. Problems
2. Coq Inductive data type
3. Cases in recursive function definitions
4. a pile of switch cases or whatever
5. Tactics -  th below -> ( [ th above ], [Pf above] -> Pf below )
6. LCF Recognizers - typ rule = [Pf up top] -> theore below -> Pf below - sometimes yuou need to give the shape of the thing you want below. Even all the above parts and the label of the rule might be insufficient. It is possible for this function to be partial / undecidable. Proof terms are a deep DSL recording these shallow moves.
7. You could make an argument for an inference rule being a relation of relations? A meta lifting.
8. rules with single things up top = executions of abstract machines

Inference rules are relations on syntactic forms?

This notion of modes is essentially the "Halfsies" notion.
Bidirectional typechecking defines the relation not between

A typing judgement is a relation between contexts, expressions, and types.
Expressions have types. Values have types. These are distinct notions.
Value as a meta notion vs Value as a subclass of expressions.

(tenv, expr, typ ) -> true
(tenv, expr) -> Maybe typ

type var = string
type expr = Var of var | Lam of var *expr | App of (expr* expr) | TT | Annot of (expr *typ)
type typ = Unit | Arr of typ* typ
type typ_ctx = (var * typ) list

type_check gamma = function
| Var v,
| TT , Unit -> true
| e, t  -> let t' = type_infer gamma e in
           t = t'
and
type_infer gamma = function
| Var v -> lookup gamma v
| Annot e t -> let c = type_check gamma e t in
               if c then t else failwith "Bad annotation"
| App f x -> let Arr (a,b) = infer_type gamma f in
             let c = type_check gamma x a in
             if c then b else fail
| _ -> failwith

Does it matter that we should return errors? I guess it does.

type_judge(Gamma, e,  type).
type_judge(Gamma, tt, unit).
type_judge(Gamma, lam(V,Body) , arr(A,B)) :- type_judge([ V -> A  | Gamma], Body , B ).
type_judge(Gamma, app(F,X) ,    )    :-

He mentioned thaty a computational interpretation of inference rules requirtes modes
Symntax directed rules can be considered as checkers, since we can pattern match on the syntax and know what to do

What interesting problem can I use?
Well, interleaved moded predicates is interesting.

Mode correctness - not a notion of bidirectional type checking.

This is an interesting idea.
Take a prolog program that is ill formed.
Consider all possible modal forms. In recursiove calls, consider all possible modes to recrusviely call. Consider all orderings of right side preds too.
This is all mechanical enough it could be considered mode synthesis.
Perhaps + some test cases

rel(A,B) :- rel(A,C), rel(C,B).

rel+-(-A,+B) :- rel--, rel--

Trim all non well moded

Maybe I hsould use mercury?
Or swipl has a mode chekcing thing probably?
<https://www.swi-prolog.org/pldoc/man?section=modes>

The fool.

It has something to do with focusing? Hmm The review paper says explicitly it does not.

<https://twitter.com/rob_rix/status/1379966266723680256?s=20> rob rix dicssuion polarity
sterling says look at sequent. negative have noninvertible left rules, positive has noninvertible right
Substructural logic (like linear)
What about bunched logic like seperation? Does that add any clairty? What is the polarity of seperating conjunction?

<https://github.com/jonsterling/dreamtt> "pedagogical" binrectional dependent tpye implentation

<https://astampoulis.github.io/blog/taksim-modes-makam/> - huh makam has modes inspired by the bidi survey

<https://twitter.com/puffnfresh/status/1377474203444637701?s=20>

<http://noamz.org/thesis.pdf>

<https://consequently.org/papers/dggl.pdf>

<https://personal.cis.strath.ac.uk/neil.ghani/papers/ghani-jfcs09.pdf>

Positive and negative types

Focusing

The two G and D categories in Harrop/Horn formula

Positivityv checking

Covaraince and contravaraince

hmm. Harper seems to suggest a positive v neagtive product type is a lazy vs strict distinction
<https://ncatlab.org/nlab/show/product+type> -

<https://ncatlab.org/nlab/show/sum+type> - need multiple sequents for

Linear logic.

Positive is "charactersize " by introductions. Plays nice with eager evaluation
Negative is "characterized" by eliminations. Plays "nice" with lazy evaluation

Introduction rules, elimination rules AND computation rules?

Proof search vs Preoof normalization semantics.

focussing and prolog

hmm harper actually has a chapter on classical logic dynamics

Bidrectional typing
Type synthesis can be interleaved with type checking

Session types to understand linear logic vs memory management
Types are things that can be attached to terms. Terms are expressions
Process calculi are some kind of terms.
<https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf>

tactics are perhaps another operational interpetation of inference rules
<https://hackage.haskell.org/package/refinery>
<https://reasonablypolymorphic.com/blog/towards-tactics/>
<https://www.youtube.com/watch?v=S0HvfXq3454&ab_channel=Z%C3%BCrichFriendsofHaskell>

# Misc

[smalltt](https://github.com/AndrasKovacs/smalltt) a demo for high performance type theory elaboration. Really good readme too
[elboration seminar](https://www.youtube.com/playlist?list=PL2ZpyLROj5FOt99f_KCxARvd1hDqKns5b)
[learn type theory](https://github.com/jozefg/learn-tt)
[simple observationsl type theory](https://github.com/bobatkey/sott)

regular propositions are basically the "constructive-content-free" parts of propositions

- <https://counterexamples.org/title.html> Counterexamples in Type Systems. Really cool resources of problems that can show up in type systems
- <https://github.com/FStarLang/FStar/issues/360> Examples that show paradoxes when using combinations of impredicative polymorphism + excluded middle + large elimination -- can only choose two <https://cstheory.stackexchange.com/questions/21836/why-does-coq-have-prop/21878#21878> Berardi's paradox
<https://github.com/coq/coq/issues/9458> future of impredicative set

[introductory type theory resources](https://twitter.com/GabriellaG439/status/1520793063467102208?s=20&t=kBQ6NNrdoK-tcIkhvRqktQ) <https://www.haskellforall.com/2022/05/introductory-resources-to-type-theory.html>

Amusingly, by mixing the type level and value level, do we end up with a situation akin to dynamic types where we often need
to carry types a runtime? Or is that mistaken?

[Type Theory in Color](https://dl.acm.org/doi/abs/10.1145/2500365.2500577) internalizes parametricity results

[Programming = proving? The Curry-Howard correspondence today Xavier Leroy](https://xavierleroy.org/CdF/2018-2019/) - so freakin good

## Books

- TAPL
- Programming Language Foundations - Harper
- [Programming in Martin Lof Type Theory](https://www.cse.chalmers.se/research/group/logic/book/book.pdf)
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- PLFA

[Resources for Teaching with Formal Methods](https://avigad.github.io/formal_methods_in_education/) mostly type thoery based
