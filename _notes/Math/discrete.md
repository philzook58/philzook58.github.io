---
layout: post
title: Discrete Mathematics
---

- [Graphs](#graphs)
- [Knots](#knots)
- [Matroids](#matroids)
- [Packings](#packings)
- [Combinatorics](#combinatorics)
- [Ramsey Theory](#ramsey-theory)
- [Logic](#logic)
- [Set theory](#set-theory)
- [Order Theory](#order-theory)
  - [Lattice](#lattice)

<https://en.wikipedia.org/wiki/Discrete_mathematics>

# Graphs

See note on graphs

# Knots

See also topology

<https://en.wikipedia.org/wiki/Knot_polynomial>

Rational Tangles - infinite series

# Matroids

See also abstract algebra

<https://en.wikipedia.org/wiki/Matroid>

"where greedy works"

<https://en.wikipedia.org/wiki/Submodular_set_function>

greedoids

<https://en.wikipedia.org/wiki/User:David_Eppstein/Matroid_Theory>

# Packings

Circle packing. Really cool. A discrete analog of complex functions

# Combinatorics

Binomial

[Generating function](https://en.wikipedia.org/wiki/Generating_function)
[generatingfunctionology](https://www2.math.upenn.edu/~wilf/DownldGF.html)
[combinatorial species](https://en.wikipedia.org/wiki/Combinatorial_species)

<https://doc.sagemath.org/html/en/reference/combinat/sage/combinat/species/species.html>
<https://hackage.haskell.org/package/species>

Shadow calculus
Sums
<https://en.wikipedia.org/wiki/Umbral_calculus>

Concrete mathematics

PIE [principle inlcusion exclusion](https://en.wikipedia.org/wiki/Inclusion%E2%80%93exclusion_principle)

[pigeon hole principle](https://en.wikipedia.org/wiki/Pigeonhole_principle)
The continuous analog.

[polya enumeration theorem](https://en.wikipedia.org/wiki/P%C3%B3lya_enumeration_theorem) polya's theory of counting

handbook of combinatorics

<https://en.wikipedia.org/wiki/Combinatorial_design>

Finite geometry

<https://en.wikipedia.org/wiki/Incidence_structure>

# Ramsey Theory

Big step up in sophistication huh
Principles that

Cody says has something to do with well quasi-orders

<https://en.wikipedia.org/wiki/Schur%27s_theorem>
<https://mathworld.wolfram.com/SchurNumber.html>
Schur number 5 = 161. 2017

[Ramsey number](https://mathworld.wolfram.com/RamseyNumber.html) solution to party problem. R(m,n) m know each other or n don't know each other.
Diagonal vs nondiagonal
2023 breakthrough on upper bound

# Logic

See lik the whole pile on logic

# Set theory

Ditto

# Order Theory

<https://en.wikipedia.org/wiki/Order_theory>

<https://en.wikipedia.org/wiki/Dilworth%27s_theorem>
Finite po-sets

<https://en.wikipedia.org/wiki/Hasse_diagram> visualizing posets

<https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Init/Order/Defs.lean>

```lean
-- an attempt
class PartialOrder (A : Type) (R : A -> A -> Prop) where
  refl : forall x, R x x
  antisym : forall x y, R x y -> R y x -> x = y
  trans : forall x y z, R x y -> R y z -> R x z

instance : PartialOrder Nat Eq where 
  refl := fun x => by rfl
  antisym := fun x y r1 _r2 => by rw [r1]
  trans := fun x y z r1 r2 => by rw [r1, r2]

def main := IO.println "hello world"

```

## Lattice

See also abstract algebra
