---
layout: post
title: Numbers
---

- [Rationals](#rationals)
- [Eudoxus Reals](#eudoxus-reals)

There are a loy of notions of "number"
Some embed inside each other.
It is interesting to see how to implement their representation in computers and how to actually evaluate their arithemtic / normalize them

Moved:
Surreal
Ordinal

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

# Eudoxus Reals

One can imagine nearly linear functions. `f(x) = Ax + r(x)` where the remainder `r(x)` is small in some sense. This is a linear approximation done all the time as an expansion. Asymptotically, if r(x) stays bounded, it matters realtively less and less. If there was some cutoff of size in the universe of numbers, some quantum, it doesn't matter.

In the proof of the irrationality of sqrt 2, one has to somehow refer to "irrationality" and "sqrt 2". To posit sqrt 2 as an enttity means you've already defined the reals. "irrationality" naively means you've already defined the rationals.

To cut the knot, you can define the question as the diophantine equation `2n^2 = m^2` does not have natural solutions. We've mangled the statement of the theorem to smething recognizable. So we've done some metalevel reasoning. This is problematic.

Likewise, there is a way to discuss reals without talking about rationals. IN the Bishop book, a constructive real is a sequence that is converging faster than 1/n more or less. `|f(i) - f(j)| <= 1/i + 1/j`. Multiplying out, `i(f(j)) - f(i)j <= 2(i + j)`

Stern Brocot trees and diophantine approximation?
