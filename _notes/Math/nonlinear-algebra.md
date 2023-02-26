---
layout: post
title: Nonlinear Algebra
---

By nonlinear algebra I mean things relating to multivariate polynomials

# Applications
- Kinematics
- Optics
- Thermodynamics, Legendre
- Global optimization
- Integer programming
- combinatorial optimization (sudoku and like)
- Circuits. Relational algebra parametrized by omega

[](https://www3.risc.jku.at/publications/download/risc_333/1998-00-00-A.pdf)
# Systems
https://github.com/algebraic-solving/msolve msolve. a C library for grobner basis and root calculations. Intresting
[msolve: A Library for Solving Polynomial Systems](https://arxiv.org/abs/2104.03572)

- [Axiom](http://www.axiom-developer.org/)
- Maple
- Maxima
- Mathematica
- Octave
- GAP
- REDUCE [redlog](https://www.redlog.eu/) quantifier elimination
- [Groebner.jl](https://github.com/sumiya11/Groebner.jl)
## Singular
[singular](https://www.singular.uni-kl.de/)
[try online](https://www.singular.uni-kl.de:8003/)
## macaulay2
## Sympy
Sympy has a ton in it
[nice little grobnr basis tutorial](https://mattpap.github.io/masters-thesis/html/src/groebner.html)

https://www.philipzucker.com/computing-syzygy-modules-in-sympy/

```python
from sympy import *

x,y,z = symbols("x y z")
f = x**2 + 1
print(dir(f))
print(f.diff(x))
```


# Univariate Polynomials
We're really good at these.
Fundamental theorem of algebra
## Polynomial division


# Linear modelling of nonlinear systems
[Numerical Polynomial Algebra by Hans Stetter](https://epubs.siam.org/doi/book/10.1137/1.9780898717976?mobileUi=0&)

## Vandermonde Matrix
The big question: Linear in what?
You can always determine a polynomial as a linear algebra problem given sample points. A polynomial can bethought of as linear in it's _coefficients_


## Companion Matrix
[wiki](https://en.wikipedia.org/wiki/Companion_matrix)
A matrix designed to have characterstic polynomial

## Sylvester matrix



#

## Homotopy Continuation
- Bertini
- homotopy.jl
- phcpack

```python
# https://ofloveandhate-pybertini.readthedocs.io/en/feature-readthedocs_integration/index.html
import pybertini
```


## Grobner Bases
See Also
- Term Rewriting

Given some polynomial, a question is 
1. is it a combination of the polynomials you have (is it in the ideal)
2. Is the set it describes a subset of the set described by your system of equations.

For 1, if you can find coefficients to actually demonstrate the combination, you're good.
Polynomial division is a way to guess/derive such coefficients. It turns out that 


You can use such a procedure to reduce a set of equations for example.

A different problem is to find a more explicit representation of the set
1. solution points
2. a parametrization of the surface. Turning constraints into a generative form is a theme all over the place. Turning hyperplanes into vertices or vice versa for example.

Monomial ordering - one can pick an ordering on the monomials. There are some sensibility conditions.

By putting the highest monomial on the lhs and the rest of the polynomial on the right `x^m - p(x) = 0 --> x^m = p(x)` and then orienting the equation `x^m -> p(x)`, it starts to look like a term rewriting system. The term ordering makes it terminating, but it is not guaranteed to be confluent (order of application of the rules matters) .
Polynomial division is a more sophisticated version of this that more or less applies the rule "many" times. It's kind of like the addition vs multiplicative for of euclidean division.
Pattern matching works modulo AC and rules of arithmetic btw.
Kind of an interesting picture.
To divide by 272, you get to remove a 200 by "adding" a -72
`200 -> -72`. The final result is the remainder. The proof or path or trace is the divisor itself.

Bases as a polynomial
2 b^2 + 7 * b + 2
rewrite system:
2 b ^2 -> -7 b - 2
10 -> b



Buchberger's algorithm
S-polynomials - any combination of polynomials that are zero is also zero. The s-polynimals try to eliminate the hghest monomials in the obvious way. This is a way to generate new identities that may have smaller coefficients or eliminate variables.

Specialization: 
- Gaussian elimination
- Euclid's algorithm



## Cylindrical Algebraic Decomposition (CAD)
[qepcad](https://github.com/PetterS/qepcad)

## NLSAT

# Modules
Linear algebra but wih rings instead of fields. You can't divide by scalars anymore.

grobner for rings with inifitniely many variables

## Free Resolution

chain complex
betti numbers


schreyer's algorithm

Koszul complex
buchssbaum-rim complex
eagon-northcott complex
somethignbaum

exterior powers
symmettric produce
tensor product
hom



# Resources
[my old link dump](https://www.philipzucker.com/dump-of-nonlinear-algebra-algebraic-geometry-notes-good-links-though/)

