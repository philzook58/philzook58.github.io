---
layout: post
title: Numbers
---

- [Rationals](#rationals)
- [Ordinals](#ordinals)
  - [Large Numbers](#large-numbers)
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

# Ordinals

Ordinals notations <https://en.wikipedia.org/wiki/Ordinal_notation> are lik systemaic ways of labelling ordinals. They don't described every posible ordinal.

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
<https://www.youtube.com/watch?v=uWwUpEY4c8o&ab_channel=PBSInfiniteSeries> PBS infinite series on hydra game

<https://en.wikipedia.org/wiki/Bachmann%E2%80%93Howard_ordinal> large countable ordinal
<https://en.wikipedia.org/wiki/Kripke%E2%80%93Platek_set_theory> weak set theory. preciative part. Separation only works on delta_0 bounded formula. I like that
<https://en.wikipedia.org/wiki/Constructive_set_theory> wow this a a whole rabbit hole
<https://ncatlab.org/nlab/files/AczelRathjenCST.pdf> notes on constructive set theory - rathjen aczel

Γ₀

<https://en.wikipedia.org/wiki/Puiseux_series> mentined that stuff generalzes this. A power series with fractional powers.
<https://en.wikipedia.org/wiki/Hahn_series> a notion of series with domain that is well ordered?

<https://en.wikipedia.org/wiki/Levi-Civita_field> contains infintesimal and infinite stuff

<https://en.wikipedia.org/wiki/Epsilon_number> fixed points of exponential maps

```python
import math
class Rational():
  def __init__(self, numb, den):
    gcd = math.gcd(num,den)
    self.num = num / gcd
    self.den = den / gcd
  def __add__(self, other):
    return Rational(self.num * other.den + other.num * self.den, self.den * other.den)
  def __mul__(self, other):
    return Rational(self.num * other.num, self.den * other.den)
  def __sub__(self, other):
    return Rational(self.num * other.den - other.num * self.den, self.den * other.den)
  def __truediv__(self, other):
    return Rational(self.num * other.den, self.den * other.num)
  def __repr__(self):
    return f"{self.num}/{self.den}"
  def __eq__(self, other):
    # or self.num * other.den == other.num * self.den
    return self.num == other.num and self.den == other.den
  def __lt__(self, other):
    return self.num * other.den < other.num * self.den

def Complex():
    def __init_(self, real, imag):
        self.real = real
        self.imag = imag
    def __add__(self, other):
        return Complex(self.real + other.real, self.imag + other.imag)

def BigNum():
  self __init__(self,n):
    self.digits = []
    while n > 0:
      self.digits.append(n % 10)
      n = n // 10
    def value(self):
      return sum([d * 10 ** i for i, d in enumerate(self.digits)])
  def __add__(self, other):
    # cheating: return BigNum(self.value() + other.value())
    res = []
    carry = 0
    for i in range(max(len(self.digits), len(other.digits))):
      s = self.digits[i] if i < len(self.digits) else 0
      o = other.digits[i] if i < len(other.digits) else 0
      res.append((s + o + carry) % 10)
      carry = (s + o + carry) // 10
  #def __mul__(self,other):
  #  res = BigNum(0)
  #  for i in range(len(self.digits)):
  #    for j in range(len(other.digits)):
  #     res += BigNum(self.digits[i] * other.digits[j]) * BigNum(10 ** (i + j))
  #  return res

class Quaternion():
  def __init__(self, c,i,j,k):
    self.c = c
    self.i = i
    self.j = j
    self.k = k
  def __add__(self, other):
    return Quaternion(self.c + other.c, self.i + other.i, self.j + other.j, self.k + other.k)
  def __mul__(self, other):
    return Quaternion(self.c * other.c - self.i * other.i - self.j * other.j - self.k * other.k,
                      self.c * other.i + self.i * other.c + self.j * other.k - self.k * other.j,
                      self.c * other.j - self.i * other.k + self.j * other.c + self.k * other.i,
                      self.c * other.k + self.i * other.j - self.j * other.i + self.k * other.c)

# https://en.wikipedia.org/wiki/Continued_fraction
# Another way of representing fractions that has nice properties.
def ContFrac():
  # this is the euclidean algorithm
  def __init__(self, num,den):
    self.coeff = []
    while num != 0:
      self.coeff.append(num // den)
      num, den = den, num % den

def golden_ratio(): # an irratinal number with infinite expansion 
  while True:
    return 1


# using built in complex and fraction
from fractions import Fraction
print(Fraction(1,10) )
print(1 + 1.j)



# another method, embedding into matrices
import numpy
def complex(r,i):
  return np.array([[r,-i],[i,r]])
```

<https://docs.python.org/3/library/numbers.html#module-numbers> abstract based classes for numbers

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
