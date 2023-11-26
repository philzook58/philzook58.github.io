---
layout: post
title: Nonlinear Algebra / Algebraic Geometry
---

- [Applications](#applications)
- [Systems](#systems)
- [Systems](#systems-1)
  - [Singular](#singular)
  - [macaulay2](#macaulay2)
  - [Sympy](#sympy)
- [Univariate Polynomials](#univariate-polynomials)
  - [Polynomial division](#polynomial-division)
- [Linear modelling of nonlinear systems](#linear-modelling-of-nonlinear-systems)
  - [Vandermonde Matrix](#vandermonde-matrix)
  - [Companion Matrix](#companion-matrix)
  - [Sylvester matrix](#sylvester-matrix)
- [](#)
  - [Homotopy Continuation](#homotopy-continuation)
  - [Grobner Bases](#grobner-bases)
  - [Cylindrical Algebraic Decomposition (CAD)](#cylindrical-algebraic-decomposition-cad)
  - [NLSAT](#nlsat)
- [Algebraic Geometry](#algebraic-geometry)
  - [Variety](#variety)
  - [Rings](#rings)
    - [Ideal](#ideal)
  - [Polynomial Maps](#polynomial-maps)
  - [Tropical Algebra](#tropical-algebra)
  - [Semidefinite Programming](#semidefinite-programming)
  - [Modules](#modules)
    - [Free Resolution](#free-resolution)
- [Resources](#resources)

By nonlinear algebra I mean things relating to multivariate polynomials

AKA maybe applied algebraic geometry

# Applications

- Kinematics
- Optics
- Thermodynamics, Legendre
- Global optimization
- Integer programming
- combinatorial optimization (sudoku and like)
- Circuits. Relational algebra parametrized by omega
- Algebraic statistics <https://en.wikipedia.org/wiki/Algebraic_statistics> <https://franknielsen.github.io/Books/CuratedBookLists.html>
- game theory
- Invariants?
[grobner bases and applications - buchberger](https://www3.risc.jku.at/publications/download/risc_333/1998-00-00-A.pdf)

# Systems

<https://github.com/algebraic-solving/msolve> msolve. a C library for grobner basis and root calculations. Intresting
[msolve: A Library for Solving Polynomial Systems](https://arxiv.org/abs/2104.03572)

# Systems

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

I hex editted singular to use libreadline.so.8. I'm a hacker now.

[A First Course in Computational Algebraic Geometry](https://sites.math.washington.edu/~billey/classes/applied.algebraic.geometry/references/BookDeckerPfister.pdf)

```bash
Singular -c "
ring R = 0, (x,y,z), lp;
poly f1 = x+y+z-1;
poly f2 = x2+y2+z2-1;
poly f3 = x3+y3+z3-1;
print f1;
quit;
"
```

## macaulay2

## Sympy

Sympy has a ton in it
[nice little grobnr basis tutorial](https://mattpap.github.io/masters-thesis/html/src/groebner.html)

<https://www.philipzucker.com/computing-syzygy-modules-in-sympy/>

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

Resolvents

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
S-polynomials
completition
comparison and application to linear solving
S-polynomials - any combination of polynomials that are zero is also zero. The s-polynimals try to eliminate the hghest monomials in the obvious way. This is a way to generate new identities that may have smaller coefficients or eliminate variables.

Specialization:

- Gaussian elimination
- Euclid's algorithm

## Cylindrical Algebraic Decomposition (CAD)

[qepcad](https://github.com/PetterS/qepcad)

## NLSAT

# Algebraic Geometry

## Variety

A surface / subset described by a set of polynomials that are zero on the set.

whole space {} - no constraints
lines
{cx +dy - a}
points
{x - a, y - b}
empty set {1} unsolvable equations

circles, hyperbolas, parabolas. Quadratc equation. Useful for distance constraints.
{x^2 + y^2 - 1}

perpendicul

cubic stuff

I mean, what more could you want?
You can form intersections and unions of these objects.
projection - not guarantted to stay an algerbaic variety. You can form a closure over approximation.

## Rings

<https://en.wikipedia.org/wiki/Ring_(mathematics)>
Something with addition and multiplication operations. Maybe _not_ division though.

examples:

- polynomials
- Integers
- Modular Integers.
- Matrices

Spectrum

localization (?). Extending the ring to allow certain denominators.
Multiplicative set - a set of ring (monoid?) elements closed under multiplication.

Quotient Rings

Rationalizing rings. A pair of ring elements quotiented by equivalence relation `ac + bd = 0`

### Ideal

an upward closed set of a ring. You can multiply by anything in the ring and still be in the ideal. You can add elements of ideal. You can generate an ideal from a given set of elements. Grobner basis is finding an equvalent basis with nice properties.
Ideal corresponds to variety I({p_i}) because multplying and adding zero points retain zero points. I({p_i}) is a kind of closure operation

Intersection of variety is union of ideals  $V(I \cup J) = V(I) \cap V(J)$ . Bigger ideals are bigger sets of constraints, hence smaller geometrical sets.

Ideal product I.J. { fg | f in I and g in J  }.  V(I.J) = V(I) cup V(J)
It performs unions. For example 2 points

Set difference can only be overapproxmated. Saturation

Projection can also only be overapproximated.

x and x^2 are both zero at x but generate different varieties. Operator V(I) is lossy. Adjunction or galois connection
Ideal is a set of polynomials. A certain kind of set.

Ideal membership question. Is given poly in ideal.
Subideal question. `{p1, p2, p3} |- {q1, q2}`

Radical ideal root(I) := {g | g^k elem I}.  The radical ideal of x^3 is x. We are getting rid of redundant powers.
Strong NullStullensatz. `I(V(I)) = root(I)`. Roughly, going to the zero set kind of removes the multiplicity in the defning polynomaisl

Prime Ideals are ideals suc that if ab is in I, then either a or b is in I.
ideal generated by x^2 is not prime, since x is not in ideal. {x,y} is.
Prime ideals <->

Minimal ideals <-> points
{x - a, y - b} is geometrically the point (a,b)

## Polynomial Maps

A^n -> A^m
Can be represented as a vector m of polymomials in variables n.
If they are linear maps, this is analog of matrix. `[ax + by, cx + dy] === [a b; c d]`
But we want to consider subsets of affine space

Maps from quotient rings.
Maps to quotient rings.

Twisted Cubic
t,t^2,t^3

Parametrization

Calculus (infinitesimals) as quotient rings. Q(x,eps)/eps^2

Nullstullensatz

Variety
Algebraic Set
Zariski Topology - closed sets are varieties. You can describe points and surfaces, which are closed sets also under typical metric topology. Consider Marshall. Mitchell benabou.

[Invitation to Nonlinear Algebra Sturmfels](https://math.berkeley.edu/~bernd/math191.html)
[Book](https://math.berkeley.edu/~bernd/gsm211.pdf)

Mumford Red Book

## Tropical Algebra

Use min plus semiring. Like the asymptotic bones of nonlinear algebra (when you go far out, big terms domainate. Take a log which is like soft-max)
Has a more combinatorial flavor which may be useful.

## Semidefinite Programming

See also notes on mathematical optimization
[semidefinite programming](https://en.wikipedia.org/wiki/Semidefinite_programming)
Positivestullensatz
Sum of squares

## Modules

Linear algebra but wih rings instead of fields. You can't divide by scalars anymore.

grobner for rings with inifitniely many variables

### Free Resolution

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
