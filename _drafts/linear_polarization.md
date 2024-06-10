---
title: Linear Logic
---

<https://bitbucket.org/fpfenning/snax/src/main/>
snax

```python
from dataclasses import dataclass
from typing import Callable
Arr = Callable

@dataclass

type Type = bool | int | Arr[Type,Type]
from enum import Enum
Expr = Enum("Expr", "Lam App Var")
def eval(e):
    match e:
        case Expr.Lam, x, body:
            return body




def eval(x):
    match type(x):
        case Arr[a,b]:





```

Linear lgic.

Linear types.

Someone has made a linear logic prover. Where can I find it.

Graham says.
A and* B says I have both and can use both.
A and+ B says both can be produced, but they use up resources. Same gamma in production rule

<https://math.stackexchange.com/questions/50340/what-is-the-intuition-behind-the-par-operator-in-linear-logic>

or+

Zena Ariola talk.
Focussing
Proof search
Two different polarities of semantics

dialog

Wadler had nice something?

Hilbert style - combinators
second order quaantifcation - modules, generics

<https://drops.dagstuhl.de/storage/00lipics/lipics-vol195-fscd2021/LIPIcs.FSCD.2021.1/LIPIcs.FSCD.2021.1.pdf> duality in action

fscad 2021 Duality in action
<https://www.youtube.com/watch?v=lyStOfi5tKw&ab_channel=FSCD2021>

coinduction is induction over contexts/observbations

How can Ic make this real.

Proof search. Djyckhoff
Is this some alternative to a BHK?

I said that callcc is kind of like backtracking or something. Can I take a SAT proof and make that so?
Sage and skeptic
evidence of falsehood
-----------

1 = 0 false

1 = 1 true

automatic phase and choice.
We can just breakdown foormula.

Game semantics.
How do I write games?

<https://www.youtube.com/watch?v=1QbRSSyKktE&t=811s&ab_channel=SociedadeBrasileiradeL%C3%B3gica>

A -> B = bigunion(W, | meet(W,A) <= B)

Don't define neg(P) as P -> bot
proof by contradiction is only a problem when you use the contradiction twice. It you use it once, you actually are comitting to a choice

Both shulman and zena use the sqrt(2)^sqrt(2)
girard algbra is analogous to heyting algerba.

antithesis transtioation

Being apart in constructive reals is not the negation of being equal.

intuiionsitc modal logic

a cleanup routine? The dstructor method.
memory management. When I pattern match into a node, do I retain it to rebuild with new stuff or destroy/free it? That's two possibilites.
Who's responsible for cleaning up?

Natural deduction has one thing on the right hand side. This is another kind of one-ness, perhaps in a different flavor thn the one-ness of linear logic

```python
%%file /tmp/
sage( As, or , Bs)
skeptic(As,  Bs)
```

```python

```
