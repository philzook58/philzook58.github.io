
# Syntax and Semantics

Type theory takes syntax more seriously than I ever realize.
It's like drawing a house. Do you draw a box with a triangle over it, or do you really look.

# Judgement

# Computation Rules

= match () with () => z  ~> z
- (fun x => x ) q = q

# Coq
QED does something serious.
Surface coq is desugared
match annnotations are 

# Equality
Extensional vs Intensional
Extensional equality collapses definitional and propositional equality.

Judgemental/Definitional / Propositional
Another way of talkin about judgementall equal is if the prof of Prop equality is just refl.

Tests
- tt = tt
- unit = unit
- 1 + 1 = 2
- x : nat |- x + 0 = x
- x : nat |- 0 + x = x
- (fun x => x) = (fun x => x)
- (fun x => x) = (fun x => tt)
- (match tt with tt => tt end) = tt
- x : unit |- tt = x
- x : unit |- match x with () => () end = ()
- x : unit |- match x with () => () end = x
- x : unit |- match x with () => () end = match x with _ => () end
- f |- f = (fun x => f x) eta
- (fun x => x) tt = tt    beta





Extensionality
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

Proof Irrelevance
Propositional extensionality implies proof irrelevance
https://coq.inria.fr/library/Coq.Logic.ProofIrrelevance.html
Axiom proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.

Computational Content

Heterogenous vs Homogenous equality

Eta equivalence - The dumb expansion? Observational Equivalence

Reduction vs Equivalence


Univalence
Implies extensionality
unit' = unit


Isomorphisms

The HoTT game <https://thehottgameguide.readthedocs.io/en/latest/getting-started/index.html>