---
layout: post
title: Non Classical Logic
---

- [Modal](#modal)
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
Modal logical operators.
Provable
Necessary

## Temporal
Eventually
## Kripke Semantics


# Partial
## Free Logic
https://plato.stanford.edu/entries/logic-free/
Free logic supports a notion of partiality. Terms aren't assumed to exists.
https://proofassistants.stackexchange.com/questions/1448/is-there-any-work-on-the-use-of-free-logic-in-proof-assistants
https://bibbase.org/network/publication/benzmller-scott-automatingfreelogicinholwithanexperimentalapplicationincategorytheory-2020 automating categor theorey is isabelle hol
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
https://plato.stanford.edu/entries/logic-substructural/
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

https://plato.stanford.edu/entries/logic-nonmonotonic/

In the theory and history of ASP this stuff shows up
- Default logic  https://plato.stanford.edu/entries/logic-nonmonotonic/#DefaLogi
- Autoepistemic logic
- 