---
layout: post
title: Topology
---
- [Point Set Topology](#point-set-topology)
  - [Continuity](#continuity)
- [Homeomorphism](#homeomorphism)
- [Algebraic Topology](#algebraic-topology)
  - [Complexes](#complexes)
  - [Homotopy](#homotopy)
  - [Homology](#homology)
  - [Morse Theory](#morse-theory)
- [Computational Topology](#computational-topology)
- [Resources](#resources)

# Point Set Topology

Munkres

[Leinster - General topology](https://www.maths.ed.ac.uk/~tl/topology/topology_notes.pdf)
bourbaki

Topology - A space equipped with a set of open sets.
<https://en.wikipedia.org/wiki/Topological_space>

```lean
-- fiddling
structure Topology (A : Type) where
  open_sets : Set (Set A)
  empty_open : (fun x => False) ∈ open_sets
  full_open : (fun x => True) ∈ open_sets
  union_open : 
  inter_open : forall x y : Set a, open_sets x -> open_sets y -> open_sets (fun z => x z /\ y z)

```

<https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Basic.lean>
<https://isabelle.in.tum.de/library/HOL/HOL/Topological_Spaces.html> isabelle

<https://github.com/math-comp/analysis/blob/master/theories/topology.v> mathcomp

<https://gist.github.com/andrejbauer/d31e9666d5f950dd8ccd> andrej bauer coq. syntehtic topology ad functions into sierpinski space <https://en.wikipedia.org/wiki/Sierpi%C5%84ski_space>
<https://github.com/coq-community/topology>

<https://en.wikipedia.org/wiki/Filter_(mathematics)>  many presentation use filters
<https://en.wikipedia.org/wiki/Filters_in_topology>

<https://en.wikipedia.org/wiki/Axiomatic_foundations_of_topological_spaces>
closure and interior operators can be axiomatized

## Continuity

Continuous functions have open preimages of open sets.

```lean

```

quotient topology. Take an equivalence relation. The quotient set is the set of equivalence classes `[z] = {x | x ~ z}`
  The quotient toplogy is the toplogy whose

# Homeomorphism

<https://en.wikipedia.org/wiki/Homeomorphism>
<https://en.wikipedia.org/wiki/Simplicial_complex_recognition_problem>

<https://en.wikipedia.org/wiki/Triangulation_(topology)>

Brouwer fixed point
<https://en.wikipedia.org/wiki/Sperner%27s_lemma>

jordan curve theorem

covering spaces

fundamental polyhedron - polyhedra schema. Those diagram with glued edges. The edges are generators

# Algebraic Topology

[algerbaic topology hatcher](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf)

[Peter May  - Algebraic Topology a concise course](http://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf)

## Complexes

- simplicial-complex - maybe the kind of obvious one. Triangulate your space.
- delta-complex <https://en.wikipedia.org/wiki/Delta_set> delta set, semisimplicial set
- CW-complex - Bread and butter
-

- simplicial set <https://en.wikipedia.org/wiki/Delta_set>
- [Kan complex](https://en.wikipedia.org/wiki/Kan_fibration)

```python
# toy around with hap definitions

class CW():

#triangle
points = [None,None,None]
edges = [(0,1), (1,2), (2,0)]
faces = [(0,1,2)] # indices refer to previous

# square
points = [None,None,None,None]
edges = [(0,1), (1,2), (2,3), (3,0)]
faces = [(0,1,2,3)] # indices refer to previous
```

Discrete finite representation of CW uses loops over previous layers. The "disk" is a polygon. This is nice compared to simplicial because there is a nicer notion of "simplifying" a space by removing redundant subdivision.

Regular vs non regular

## Homotopy

Deformation Retract- $f_t : X -> X$ s.t. $f_0 = id$ and f_1 = A and f_t(A) = A for all t. It leaves A alone for all t. <https://en.wikipedia.org/wiki/Retraction_(topology)>. Retraction is projection to subspace that preserves all points in subspace.

<https://en.wikipedia.org/wiki/Inclusion_map>

## Homology

## Morse Theory

# Computational Topology

<https://en.wikipedia.org/wiki/Computational_topology>
<https://www.computop.org/> lots of cool programs

[computatonal toploggy edelsbrunner harer](https://www.maths.ed.ac.uk/~v1ranick/papers/edelcomp.pdf)
[notes](https://www.ams.org/meetings/shortcourse/zomorodian-notes.pdf)

[haskell rewrite of kenzo](https://github.com/mvr/at)

HAP GAP <https://docs.gap-system.org/pkg/hap/www/index.html>
graham ellis. Book
<https://www.youtube.com/watch?v=UMpTTuRdMA0&ab_channel=InstitutFourier>

<http://snappy.computop.org/> snappea for 3 manifolds. python bindings
<http://snappy.computop.org/verify_canon.html> canonical retriangulation / cell decoomposition
geometrization theorem
dehn-filling
There's like a canonical geometrical surface? And then metrical things like volume are cannical?

uniformizaton

<http://chomp.rutgers.edu/> chomp computational homology

exact reals?
hott?

toploogical data anaysis
persistent topology

seifert

computational group theory
MAF <https://maffsa.sourceforge.net/manpages/MAF.html>
KBMAG
automata to describe the multiplication operation

# Resources
