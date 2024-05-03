---
layout: post
title: Numbers
---

- [Rationals](#rationals)
- [Surreal Numbers](#surreal-numbers)
- [Hyperreals](#hyperreals)
- [Eudoxus Reals](#eudoxus-reals)

There are a loy of notions of "number"
Some embed inside each other.
It is interesting to see how to implement their representation in computers and how to actually evaluate their arithemtic / normalize them

# Rationals

Stern Brocot <https://en.wikipedia.org/wiki/Stern%E2%80%93Brocot_tree>
binary search
mediant (a + c)/(b + d) is between a/b and c/d. vector addition on ration representation
Is it a game? Is this dstint from continued fractions?
<https://www.ams.org/publicoutreach/feature-column/fcarc-stern-brocot> clock making and stern brocot

```python
class SternBrocot():
  def __init__(self,x):
    a = Fraction(0,1)
    b = Fraction(1,1)
    self.dirs = [] # stern brocot represents fraction as sequence of L/R
    while num / den != a / b:
      mediant(a,b)
      if x < mediant
        self.dirs.append('L')
        a = c
        b = d
      elif x > mediant:
        self.dirs.append('R')
        a = c
        b = d
      else:
        break

```

continued fractins - Adding? Do I have t go down and then up? A "lens" into the whole and fractional part?
lanczos algorithm is best ratinal approximatin to eigenvalues? Computational Linear algebra over infinite vectors. What can be done? Can invert triangular matrices. Can of course take increasing finite slices. increasing low rank update?

best ratinal apporxmation

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

Von Neumann

```python
_univ = 

def internset(x):
  x = frozenset(x)
  if x in _univ:
    return _univ[x]
  else:
    _univ[x] = x
    return x
# von neumann
zero = internset([])
def succ()
def univ():
  return internset(_univ)
# https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory

def pair(a,b):
  return frozenset([a,b])
def order_pair(a,b):
  return frozenset(frozenset({a}), frozenset({a,b}))

# separation axiom
def separate(A, P):
  return frozenset({x for x in A if P(x)})

from itertools import chain, combinations

def powerset(iterable):
  #https://stackoverflow.com/questions/1482308/how-to-get-all-subsets-of-a-set-powerset
  powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
  s = list(iterable)
  return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))

# NBG class? == P, just a indicator function.
```

```python

def surreal(a,b):
  if (a,b) in univ:
    return univ[(a,b)]
  else:
    univ[(a,b)] = (a,b)
    return (a,b)
empty = frozenset()
zero = surreal(empty,empty)
one = surreal(frozenset(zero),empty)

class Surreal():
  def __init__(self, a, b):
    self.a = a
    self.b = b
  def __le__(self, other):
    #return self.a <= other.b
  #def __add__(self)

# surreal as pair of game trees
tictactoe = [[],[],[]]




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

<https://www.youtube.com/@elwynberlekamp5528> berlekamp videos

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
What is a "large" set?

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
