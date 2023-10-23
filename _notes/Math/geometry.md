---
layout: post
title: Geometry
---

See also:
- Graphics

# Projective
Look at computer vision


## Homogenous Coordinates
Make one more coordinate then you need. You decide the overall scale no longer matters. The point  (1,3) is the same point as (2,6).
The simple model is that of a pinhole camera. If the pinhole is at (0,0,0), then all point light sources on a line stretching through the pinhole make equivalent images.
It strangely turns out that these coordinates have beautiful properties.
## Duality
In homogenous coordinates, 
## Axiomatic

# Euclidean
Classical geometry. Euclidean lines and points and circles

# Algebraic


https://en.wikipedia.org/wiki/Blowing_up
[birational](https://en.wikipedia.org/wiki/Birational_geometry)


Griffiths, Phillip; Harris, Joseph (1978). Principles of Algebraic Geometry.
Hartshorne, Robin Algebraic Geometry. 
https://math.stackexchange.com/questions/1748/undergraduate-algebraic-geometry-textbook-recommendations?noredirect=1&lq=1 

# Differential
https://en.wikipedia.org/wiki/Manifold
https://juliamanifolds.github.io/Manifolds.jl/stable/index.html https://arxiv.org/pdf/2106.08777.pdf
[manopt.jl](https://www.youtube.com/watch?v=thbekfsyhCE&ab_channel=TheJuliaProgrammingLanguage)
[manifolds.jl](https://www.youtube.com/watch?v=md-FnDGCh9M&ab_channel=TheJuliaProgrammingLanguage)
"The seven major libraries for
differential geometry in Python are Pymanopt (Townsend et al., 2016), Geomstats (Miolane
et al., 2020), Geoopt (Kochurov et al., 2020), TheanoGeometry (Kühnel and Sommer, 2017),
Jax Geometry (Kühnel and Sommer, 2017), Tensorflow RiemOpt (Smirnov, 2021), and
McTorch"

Visual differential geometry
Functional differential geometry

Differential forms

coordinate free
abstract manifold type
```
type M = { 
    [(string, I , Rn -> M) ] 
    [string,string, I,I ,Rn -> Rn] I is interval of overlap
    https://en.wikipedia.org/wiki/Atlas_(topology)
}
type M = {Rn, [Rn -> R] } # intersection of constrain maps embedded in higher Rm

x : M -> R


```

## Curvature

# Discrete Geometry

# Convex Geometry
- See convex optimization





# Automated Theorem Proving

https://www.routledge.com/Handbook-of-Geometric-Constraint-Systems-Principles/Sitharam-John-Sidman/p/book/9781498738910
handbook of geometric constraint systems

https://www.geogebra.org/?lang=en
https://link.springer.com/article/10.1007/s10817-015-9326-4

[A Deductive Database Approach to Automated Geometry Theorem Proving and Discovering](https://www.researchgate.net/profile/Xiao-Shan-Gao/publication/220531926_A_Deductive_Database_Approach_to_Automated_Geometry_Theorem_Proving_and_Discovering/links/00b7d51a5db8fde97d000000/A-Deductive-Database-Approach-to-Automated-Geometry-Theorem-Proving-and-Discovering.pdf)

[Automated reasoning in geometry theorem proving with Prolog](https://www.academia.edu/download/35058350/geometry.pdf)

[Affine geometry of collinearity and conditional term rewriting](https://link.springer.com/chapter/10.1007/3-540-59340-3_14) A good maude example probably

[TGTP](http://hilbert.mat.uc.pt/TGTP) thouands of geometrical problems

[basic properties of triangles isabelle](https://www.isa-afp.org/entries/Triangle.html)

https://dblp.org/pid/18/4206.html jacques fleuriot


https://www.usna.edu/CS/qepcadweb/B/QEPCAD.html 


https://github.com/lucaferranti/GeometricTheoremProver.jl https://www.youtube.com/watch?v=q_08LE4UOU8&ab_channel=TheJuliaProgrammingLanguage
Ritt-Wu method. Use polynomial divisiion once? Seems kind of weak, but maybe
[Automated Geometric Theor omated Geometric Theorem Proving: W ving: Wu's Method s Method ](https://scholarworks.umt.edu/cgi/viewcontent.cgi?article=1034&context=tme)

https://www.osti.gov/servlets/purl/1761359 Prove-It
https://sandialabs.github.io/Prove-It//
https://github.com/sandialabs/Prove-It

https://www.andrew.cmu.edu/user/avigad/Students/rojas_thesis.pdf EuclidZ3

