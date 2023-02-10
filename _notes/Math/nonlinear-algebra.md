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
- combinatorial optimization (sudoku and like)

# Systems
## Singular
## macaulay2
## Sympy
Sympy has a ton in it
## Maxima
- [Axiom](http://www.axiom-developer.org/)
- Maple
- Mathematica
- Octave
- GAP
- REDUCE [redlog](https://www.redlog.eu/) quantifier elimination
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

Buchberger's algorithm
S-polynomials



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

https://github.com/algebraic-solving/msolve msolve. a C library for grobner basis and root calculations. Intresting