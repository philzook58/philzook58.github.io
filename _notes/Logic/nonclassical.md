---
layout: post
title: Non Classical Logic
---

- [Modal](#modal)
  - [Provability Logic](#provability-logic)
  - [Temporal](#temporal)
  - [Kripke Semantics](#kripke-semantics)
- [Partial](#partial)
  - [Free Logic](#free-logic)
- [Intuitionistic](#intuitionistic)
- [Substructural Logics](#substructural-logics)
  - [Linear](#linear)
  - [Separation Logic](#separation-logic)
    - [Bunched Logic](#bunched-logic)
- [Non-monotonic logic](#non-monotonic-logic)

# Modal
<https://en.wikipedia.org/wiki/Modal_companion>

Modal logical operators.
Provable
Necessary

Why modal logic? You can kind of express in forist order logic
"
You can do something like that: <https://en.wikipedia.org/wiki/Standard_translation>
But I think you kinda lose some fine structure this way.
Like, there are some really nice correspondences between different modal axioms and different structural properties that their frames have. You might be able to recover that in the first-order context (not sure), but you'd probably be implicitly retranslating back into Kripke frames.
There are even some properties that you can capture, in some sense, with modal semantics that you can't capture with first-order logic. Like, you can't write down a first-order set of axioms involving some relation symbol R that are satisfied in all and only the models where R is interpreted by a well-founded relation. But you can write down a modal axiom satisfied in all and only the unvalued kripke frames where the accessibility relation is (transitive and) well-founded. <https://plato.stanford.edu/entries/logic-provability/#CharModaSoun> (edited)
It's absolutely wild that that axiom corresponds to Lob's theorem.
This guy: <https://en.m.wikipedia.org/wiki/Johan_van_Benthem_(logician)>
Is probably the real person to talk to. He's got a couple of theorems that give pretty precise characterizations of which first order formulas are equivalent to translations of modal formulas. Here's a decent gloss: <https://plato.stanford.edu/archIves/spr2010/entries/logic-modal/#Bis>
There's also a description of some related results in his thesis: <https://eprints.illc.uva.nl/id/eprint/1838/>
There are surprisingly few clear google-able statements of the result described in the SEP entry though.

I was reading that lamport book on the plane, and of course we discusses temporal logic or tla, but with a very fol first approach. And I was pondering how to treat it in knuckledragger, since I can’t really import a modal logic solver off the shelf to my knowledge
And I just lose the thread on what even is the point of modal logic
I can pull in off the shelf model checkers I guess
But directly describing the signals and properties in z3 seems easier and easier to explain
But maybe the modal abstraction avoids reasoning that is fruitless
Its a higher level perspective on the problem
Cody mentioned that propositional temporal logic is decidable, which is not obvious in its fol quantifier form
This is related to you can’t describe the transitive closure of a relation in fol?
But what if you bolt it in <https://microsoft.github.io/z3guide/docs/theories/Special%20Relations/> also adts have some fixed point ness to them. z3 special relations

I think it is fair to say that it's related to the undefinability of transitive closure in FOL. Here are axioms for a (reflexive) transitive closure in a propositional logic with two modalities:
■P <-> P ∧ □■P
P ∧ ■(P → □P) → ■P
A frame satisfies these IFF the accessibility relation associated with ■ is the transitive reflexive closure of the accessibility relation associated with □. (I kinda lifted these from <https://plato.stanford.edu/entries/logic-dynamic/> - that's another nice example of a modal logic that's decidable, apparently with some interesting complexity bounds, it's EXPTIME-complete).
This looks rather fun, for getting at the relationship between modal logic and monads in type theory: <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/jfp.pdf>
TLA+-adjacent solvers: <https://github.com/black-sat/black>
"

## Provability Logic

<https://plato.stanford.edu/entries/logic-provability/>
See proof theory

Lobs theorem <https://en.wikipedia.org/wiki/L%C3%B6b%27s_theorem>

Boolos - logic of provability

<https://dl.acm.org/doi/pdf/10.5555/1029786.1029818> logicians who reason about themselves

## Temporal

Eventually

## Kripke Semantics

# Partial

## Free Logic

<https://plato.stanford.edu/entries/logic-free/>
Free logic supports a notion of partiality. Terms aren't assumed to exists.
<https://proofassistants.stackexchange.com/questions/1448/is-there-any-work-on-the-use-of-free-logic-in-proof-assistants>
<https://bibbase.org/network/publication/benzmller-scott-automatingfreelogicinholwithanexperimentalapplicationincategorytheory-2020> automating categor theorey is isabelle hol
inclusive logic

- Partial horn logic
- GATs Generalized algerbaic theories - Catlab.jl
- Essentially algerbaic theories

Membership equality logic & order sorted logic are two things in maude. See term rewriting notes

# Intuitionistic

Also see:

- type theory
- proof theory

Intuitionistic vs constructive.
Giving a recipe how to construct a thing (possibly algorithmic) vs saying that it is inconsistent for the thing to not exist.
These are not the same notion.

There's also a feeling of "observation" a bit. The big hang up is certain sectors of our technical culture are saturated by boolean reasoning. Facts are true or false.
Proven vs unproven is not the same thing as true or false. An unproven thing may become true if you run your inference a little longer, or perhaps if you add new reasonable axioms.
If I only tell you the law of addition that `0 + x = x`, can you tell me that `x + y = y + x`? No, you need more stuff. In this context the fact being "true" is a very relative thing to your axioms, inference rules, and processing time.
Now we all kind of agree natural numbers exist. Are these sentences true in the naturals? Yes. In many reasonable systems to model what the naturals might mean, these laws are derivable.
But if you get a little more crazy with your questions you start asking hard stuff where it isn't clear that all reasonable systems can derive these facts. Then truth becomes way more relative feeling, in analogy to the simple intentionally limited case.

# Substructural Logics

<https://plato.stanford.edu/entries/logic-substructural/>
The context Gamma is not set-like.
Explicit swapping necessary - list like
Explicit duplication - multi-set like. Useful for modelling resource usage. Linear logic

## Linear

finvect model
<https://www.pls-lab.org/en/Vector_space_models_of_Linear_Logic>
<https://www.seas.upenn.edu/~sweirich/types/archive/1992/msg00047.html>

Cyclone
Regions
Tofte

Linear logic is resource sensitive. It is vaguely similar to

- Rust lifetimes
- Quantum information nad the no-cloning theorem

Can these be made precise?

It is realted to seperation logic in that both are substructural logics and in

It gives interesting insight into the proof search process of prolog and ilk.

Frank Pfenning had a funky example involving making change.

[Chris Martens thesis](http://www.cs.cmu.edu/~cmartens/thesis/) Interactive worlds with linear logic
[strange loop talk](https://www.youtube.com/watch?v=rICThUCtJ0k&ab_channel=StrangeLoopConference)
[ceptre](https://www.youtube.com/watch?v=bFeJZRdhKcI&ab_channel=StrangeLoopConference)
Celf
[Ceptre](https://github.com/chrisamaphone/interactive-lp)
stateful computation "frame property" all the stuff that strays the same
purely functional - pass entire state
datalog - database update
celf - state update

Idris2
Linear haskell
ATS
Rust
QTT - Quantitative type theory

Mercury has linear types of some kind

What if I modelled destructive rewrite rules in egglog as linear logical?
Is a linear logic programmign langguae a good candidate for a prolog metainterpreter?

## Separation Logic

### Bunched Logic

# Non-monotonic logic

<https://plato.stanford.edu/entries/logic-nonmonotonic/>

In the theory and history of ASP this stuff shows up

- Default logic  <https://plato.stanford.edu/entries/logic-nonmonotonic/#DefaLogi>
- Autoepistemic logic
-
