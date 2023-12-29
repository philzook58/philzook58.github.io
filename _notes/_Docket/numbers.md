---
layout: post
title: Numbers
---

- [Ordinals](#ordinals)
  - [Large Numbers](#large-numbers)
- [Surreal Numbers](#surreal-numbers)
- [Hyperreals](#hyperreals)
- [Eudoxus Reals](#eudoxus-reals)

# Ordinals

Ordinals are a generalizatin of numbrs

Countable ordinals.
1 .... omega is countabe. 0 -> omega, 1 -> 0, 2 -> 1 ... is an enemeration. It isn't an order repsecting enumeration though.
So "infinite" numbers can be finitely represented. `type omega_plus_1 = Omega | Fin of nat`. We are used to this from floats for example
So polynomials of omega is maybe a first place to state. Those are implementable as typical lists of coefficients.  They have funky addition and mult properties (funky mult happens in matrices and quaternions, but noncommutative addition is more unusual). But then ordinals typically allow going up to new stuff (exponentiation and beyond).

<https://www.khoury.northeastern.edu/home/pete/pub/cade-algorithms-ordinal-arithmetic.pdf> algorithms for ordinal arithemtic. ACL2

<https://link.springer.com/chapter/10.1007/BFb0023868>  Ordinal arithmetic with list structures dershowitz reingold

Termination as mapping into ordinals. Measure is the map. Simple ones into integers. Lexicographic and w^n

<https://mathoverflow.net/questions/456649/lists-as-a-foundation-of-mathematics> lists as foundation of mathematics.

<https://dl.acm.org/doi/10.1145/3372885.3373835> Three equivalent ordinal notation systems in cubical Agda
<https://www-sop.inria.fr/marelle/gaia/RR8407.pdf> Implementation of three types of ordinals in Coq <https://www-sop.inria.fr/marelle/gaia/>

```coq
(* cons(a,n,b) = w^a(n + 1) + b  *)
Inductive T1 : Set :=
zero : T1
| cons : T1 -> nat -> T1 -> T1
```

<https://github.com/sympy/sympy/issues/8668> sympy issue on ordinal arithmetic
<https://github.com/sympy/sympy/blob/master/sympy/sets/ordinals.py>

```python
from sympy.sets.ordinals import *
w = omega
z = ord0
print(3 + w + 2 * w)
print(2 * w)
```

<https://github.com/ajcr/transfinite> `pip instal transfinite` python package

```python
# https://github.com/ajcr/transfinite/blob/master/notebooks/ordinal_arithmetic_basics.ipynb notebook
from transfinite import w, factors
print(w*w + 1)
print(1 + w)
print(dir(w)) # addend', 'coefficient', 'exponent', 'is_delta', 'is_gamma', 'is_limit', 'is_prime', 'is_successor'
print(w.is_limit()) # true
print(w.is_delta()) # mutliplicatively indecomposable
print((w + 1).is_limit()) #false
print(w ** w)
print( w <= w)
print(repr(w))
fs = factors(w*w) 
print(dir(fs)) # as_latex', 'factors', 'ordinals', 'product'

# based in cantor normal form https://github.com/ajcr/transfinite/blob/master/transfinite/ordinal.py
#          (exponent)
#         ^
#        w . (copies) + (addend)
```

Prime ordinals and facotring

<https://web.mit.edu/dmytro/www/other/OrdinalArithmetic.py> <https://web.mit.edu/dmytro/www/other/OrdinalNotation.htm>

<https://www.jstor.org/stable/20118717> rathjen  2006 Theories and Ordinals in Proof theory
Rathjen the art of ordinal analysis <https://www1.maths.leeds.ac.uk/~rathjen/ICMend.pdf>

<https://github.com/coq-community/hydra-battles>  <https://coq-community.org/hydra-battles/doc/hydras.pdf> book
chapter 3 is on ordinals in coq

<https://en.wikipedia.org/wiki/Goodstein%27s_theorem> - hydra games. unprovable in peano arith
<https://math.andrej.com/2008/02/02/the-hydra-game/> kirby and paris Accessible Independence Results for Peano Arithmetic
<http://www.madore.org/~david/math/hydra.xhtml> javascript of the game
hydra is kinda remniscent of hackenbush

<https://en.wikipedia.org/wiki/Bachmann%E2%80%93Howard_ordinal> large countable ordinal
<https://en.wikipedia.org/wiki/Kripke%E2%80%93Platek_set_theory> weak set theory. preciative part. Separation only works on delta_0 bounded formula. I like that
<https://en.wikipedia.org/wiki/Constructive_set_theory> wow this a a whole rabbit hole
<https://ncatlab.org/nlab/files/AczelRathjenCST.pdf> notes on constructive set theory - rathjen aczel

Γ₀

<https://en.wikipedia.org/wiki/Puiseux_series> mentined that stuff generalzes this. A power series with fractional powers.
<https://en.wikipedia.org/wiki/Hahn_series> a notion of series with domain that is well ordered?

<https://en.wikipedia.org/wiki/Levi-Civita_field> contains infintesimal and infinite stuff

<https://en.wikipedia.org/wiki/Epsilon_number> fixed points of exponential maps

## Large Numbers

name the smallest numnber.

tree(3) <https://www.youtube.com/watch?v=3P6DWAwwViU&ab_channel=Numberphile>
graham's number

# Surreal Numbers

HACKENBUSH: a window to a new world of math <https://www.youtube.com/watch?v=ZYj4NkeGPdM&t=2818s&ab_channel=OwenMaitzen> Owen Maitzen rip.

```python

zero = (None,None)
one = (zero,None)
two = (one,None)
three = (two,None)
neg_one = (None,zero)
neg_two = (None,neg_one)
neg_three = (None,neg_two)

```

Is there a normal form? That helped ordinals a lot

Hackenbusch
Nimbers
Combinatorial Game theory
Aaron N. Siegel's "Combinatorial Game Theory

Fraise games. Ehrenfeucht-Fraïssé  <https://www.youtube.com/watch?v=ZS8PfP_JCdA&ab_channel=ThomasKern>
<https://trkern.github.io/efg.html>

`{|}` sets of available moves. Tic tac toe as a number ("ontinutatons") So programming languages have game semantics. Could one make a PL game?
*, uparrow, double up, eps, omega.
`*` is like a cloud

The game of quantifiers is how we discuss reals. Connection? We are reifying

on off dud
oof hi lo
These are non well founded? Or just

# Hyperreals

Goldblatt

Compactness is important here? Huh.

Adding

Trying to make infinitesimals rigorous

Rings can have things like eps^2 = 0 by taking quotient rings.
Something with R as a subfield.

Constructing a model of hyperreals. Infinite sequences of reals. Quotient by equivlanec e relation of agreeing on cofinite set.

A finite list of disagreement points

```
equiv(a,b,l) = forall n, a[n] = b[n] | n in l 
```

More equational than classical presentation?

R is unique complete ordered field. So R*

Transfer principle

Ultrafilter.
Ultrafilter as a notion of truth. Relation to topos? Modal logic? Intuitionstic logic?

Ultrapower.

Internal set theory

Adding a "standard" predicate to set theory. There is a notion of standard elements vs nonstandard elements.
This has a connection to standard models of constructions like the reals or naturals, which by the weakness of power of description of first order logic, the axims often allow other models besides the standard one.

This has some flavor of the method of "junk" elements used to model partial functions using total functions as I've played around with in category theory.

Nonstandard elements are hard to grasp because whenever you get concrete hold f somthing, it tends (is always?) standard.

I think I've seen it mentioned that maybe "standard" is somehow talking about a fluid boundary of described or construct elements. If I keep around an eps smaller than any number I've considered so far, and maybe go back and fix it up as I go should I ever bring in anything smaller? I do kind of feel like an approximate equality of finite difference is sufficient

Nonstandard models of peano <https://en.wikipedia.org/wiki/Non-standard_model_of_arithmetic>
We can keep adding x > n for any n to the axiom set and stay consistent. The forall n is in the metalogic. By compactness, we can add the forall n into the object logic and stay consistet?

Hypernaturals - a construction of the hypernatural is sequences of naturals identified under a ultrafilter (a "large set"). It's weird that allowing just a little disagreement helps

HyperRationals

Naive Infinitesimals
The reals are a subfield of the hyperreals.
There exist infinittesimals which are smaller than

The "standard" function behaves like a kind of rounding.

Distincting between equality and approximation equality.
a ~ b == st(a) = st(b)

st pushes through regular operations (+, -, ...). So it is a homomorphsim of sorts.
st(eps) = 0

lim = x ~ c /\ x != c -> lim(t(x)) = t(c)
continuity is x ~ y -> f(x) ~ f(y)

# Eudoxus Reals

One can imagine nearly linear functions. `f(x) = Ax + r(x)` where the remainder `r(x)` is small in some sense. This is a linear approximation done all the time as an expansion. Asymptotically, if r(x) stays bounded, it matters realtively less and less. If there was some cutoff of size in the universe of numbers, some quantum, it doesn't matter.

In the proof of the irrationality of sqrt 2, one has to somehow refer to "irrationality" and "sqrt 2". To posit sqrt 2 as an enttity means you've already defined the reals. "irrationality" naively means you've already defined the rationals.

To cut the knot, you can define the question as the diophantine equation `2n^2 = m^2` does not have natural solutions. We've mangled the statement of the theorem to smething recognizable. So we've done some metalevel reasoning. This is problematic.

Likewise, there is a way to discuss reals without talking about rationals. IN the Bishop book, a constructive real is a sequence that is converging faster than 1/n more or less. `|f(i) - f(j)| <= 1/i + 1/j`. Multiplying out, `i(f(j)) - f(i)j <= 2(i + j)`

Stern Brocot trees and diophantine approximation?
