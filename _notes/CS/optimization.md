---
layout: post
title: Optimization
tags: optimization
description: my notes about optimization
---

- [Linear Programming](#linear-programming)
  - [Tricks](#tricks)
    - [Encoding equality in terms of inequality](#encoding-equality-in-terms-of-inequality)
    - [Making the objective a variables](#making-the-objective-a-variables)
    - [Absolute value encoding](#absolute-value-encoding)
    - [Minimax encoding](#minimax-encoding)
    - [Linear in _what_?](#linear-in-what)
    - [Absolute values regularization tends to make solutions sparse.](#absolute-values-regularization-tends-to-make-solutions-sparse)
  - [Applications](#applications)
- [Convex Optimization](#convex-optimization)
- [Duality](#duality)
  - [Duals as Proof](#duals-as-proof)
  - [Geometrical Perspective](#geometrical-perspective)
  - [Lagrange Multipliers and Legendre Transformation](#lagrange-multipliers-and-legendre-transformation)
- [Bilevel programming](#bilevel-programming)
  - [method 1 KKT condition](#method-1-kkt-condition)
- [Quadratic Programming](#quadratic-programming)
- [Conic Programming](#conic-programming)
- [Stochastic programming](#stochastic-programming)
- [Semi definite programs](#semi-definite-programs)
  - [Applications](#applications-1)
  - [Sum of Squares](#sum-of-squares)
- [Complementarity Problems](#complementarity-problems)
- [Mixed Integer](#mixed-integer)
  - [Big-M](#big-m)
  - [Encoding boolean functions/relations](#encoding-boolean-functionsrelations)
  - [Piecewise linear encodings](#piecewise-linear-encodings)
  - [Unrolling time](#unrolling-time)
- [Resources](#resources)

# Linear Programming

$$ \min c^T x $$
$$ Ax \le b $$

## Tricks
### Encoding equality in terms of inequality
$$ Ax \le b $$ and Ax \ge b $$ gives a equality
### Making the objective a variables
Make a new variable $$ t $$ and add constraint $$ t = c^T x $$. Now you can minimize $$ t $$ instead.
### Absolute value encoding
min \sum_i |c_i^T x|

You can create a new variable t_i for each absolute value term
replace with

min \sum_i t_i
\forall_i t_i <= c_i^T x <= t_i

### Minimax encoding
A similar feeling trick

min ( max_i c_i^T x)

create a _shared_ bound t

min t
\forall_i c_i^T <= t

Because minimizing t tries to push against these new constraints, t will end up being the maximum of them. The constraint correspond to this will be tight, whereas the others will be slack.
This trick does not generalize as much as one might naively hope. Nested optimization is often difficult. See bilevel optimization.

### Linear in _what_?

### Absolute values regularization tends to make solutions sparse.


## Applications
- least absolute value optimization
- Relaxations of discrete optimization problems
- Network flow
- how do strings hang
- Contact constraints

# Convex Optimization

# Duality

Cody seems to be under an impression that I understand duality in the context of convex optimization and linear programming. I don't know nothing about it I suppose.

A convex optimization problem is the following

$latex \min \phi(x)$

$latex g(x) \ge 0$

Where both $latex \phi$ and $latex g$ have to be convex functions. Convex means bowl shaped. 

For smooth functions, convex means that the tangent line globally underestimates the value of the function itself.

More generally it means that $latex 0 \le \lambda \le 1 \rightarrow \phi(\lambda x + (1 - \lambda)y) \le \lambda \phi(x) + (1 - \lambda) \phi(y)$

This matters because corners show up pretty often in convex optimization.

This condition is sort of a sister inequality version of the more familiar condition of linearity. $latex f(\alpha x + \beta y) = \alpha f(x) + \beta f(y)$. It allows you to pull stuff out.

These problems are basically polynomial time solvable (i.e. fast) . The reason this is true is that local good moves are global good moves because of the convexity condition. Roughly greedy works, greedy often being gradient descent or a Newton method (using second derivatives). The simplex algorithm is also a greedy algorithm.

A special but very important case of convex optimization is that of linear programming

$latex \min c^T x $

$latex Ax \ge b$

Geometrically this is trying to find the farthest point in the $latex -c$ direction that is in the polytope described by $latex Ax\ge b$. A polytope is a shape made of a bunch of flat sides, the higher dimensional analog of a polygon. Every row of the matrix A correspond to a face of the polytope. The row is the normal vector to the face and the entry in b controls an offset from the origin. 

Another way of phrasing this is that we are in a polytope that is the conjunction (And) of the half spaces described by the rows of A.

Linear programming is so important because basically it straddles the discrete and the continuous. Polytopes have a finite number of discrete corners.

There is always corner of the polytope is always at least as good as any point on a face as far as the objective is concerned. This is the seeds of the simplex algorithm

In principle, a Bogo-simplex algorithm would be to take every d possible selections of the rows of A, find the vertex that describes via Gaussian elimination, check that this vertex is in the half space of all the other vectors, and then evaluate the objective on it. This would be an insane combinatorial explosion. The remarkable thing is that this process is not necessary. 

Nevertheless, this procedure demonstrates that the solutions are going to be fractions.

Suppose you have an optimal solution to an LP. How do you know it is optimal? There is a simple proof.

##  Duals as Proof

I can derive new inequality bounds by combining the rows of A. When you add together inequalities, you have to multiply by positive coefficients only, or you will flip the direction of the inequality. If I left multiply by a vector $latex l \ge  0$ I can derive new bounds from the assumption that you are in the polytope.  This is similar to deriving new _equations_ from sum of the rows of a matrix that occurs during Gaussian elimination.

$latex l^TAx \ge l^Tb$

How can we use that to find a bound on the objective. Well if we add the additional constraint that $latex A^T l = c$ then we derive the new bound $latex l^TAx = c^T x\ge l^Tb$. So by fiddling with the values of l, we may try to create better and better lower bounds on the objective function derived from the polytope constraints.

If I can exhibit both an $latex l^*$ and and $latex x*$ such that $latex c^T x = l^*^T b$ then I'm golden no matter how I cheated and killed to find them.

It is a remarkable fact that these vectors are in fact guaranteed to exist. That is the content of strong duality and Farkas Lemma.

Sometimes the dual is called a certificate of optimality. But we can also consider it to be a proof object. It is data that somehow encodes a particular kind of linear sum of inequalities proof.

##  Geometrical Perspective

As I said above, each row of the matrix A corresponds to a half space. 

More generally, any convex set can be considered the as the convex union of all it's points or dually as the intersections of all the half spaces that fully include the object.

Half spaces can be coordinatized as a normal vector l and an offset parameter r such that $latex \{ x | l^T x \ge r \}$.

Looking at only the extremal bits (the boundary), a convex set is the convex hull of it's boundary and the set is the envelope of it's extremal halfspaces (those that actually touch the set).

$latex \{ x | x \elem C \}$ $latex \{ (l ,b)| \forall x \in C, l^T x \ge b \cap \}$

$latex \{l | l \in C^* \}$    $latex \{x | \forall l \in C^*  \}$

In the affine geometry we're considering, these two things don't 

The duality becomes much cleaner when we remove the offsets and work in projective geometry. Everything becomes homogenous coordinates and instead of talking about convex sets, we talk about conic sets.

We can recover the affine considerations by taking a slice of the cone z = 1. This is the standard way of going back and forth between homogenous coordinates and regular coordinates.

A Cone is a set that is closed under non-negative combinations of it's points. The dual cone is the set of all half spaces at the origin that fully contain the primal cone.

## Lagrange Multipliers and Legendre Transformation

# Bilevel programming
[Review on Bilevel optimization](https://arxiv.org/pdf/1705.06270)
[Gentle and incomcplete introduction to bilevel optimization](http://www.optimization-online.org/DB_FILE/2021/06/8450.pdf)
Bilevel programming is a natural idea of modelling nested optimization problems. They occur when you want to optimize given that someone else is optimizing
For example, suppose you want to optimize a trajectory for worst case error forces. You minimize a cost while errors are trying to maximize it.
Or the two problems can have unrelated objectives


## method 1 KKT condition
Optimal points of the lower problem hav KKT conditions ~ gradient = 0. These are equality constraints. This turns it into a nonlinear optimization problem.
It is not entirely clear to me that any point that satisfies kkt conditions is necessarily a global optimum. That sounds ok... hmm

KKT conditions include complementarity conditions, converting into a complementarity problem. This can in turn perhaps be encoded into MIP. Or possibly you might end up with a system of polynomial equations which can be treated (at small scale) using homotopy continuation methods or other algebraic methods.




# Quadratic Programming
# Conic Programming


# Stochastic programming

# Semi definite programs
optimization over positive semidefinite matrices. Very powerful

## Applications
- lyapunov matrices. You need to show that something is stable. The interesting example is that you have linear dynamical system and a discrete set of possible dynamics. You can find a common lyapunov matrix to all of them 
- density matrices
- sum of squares polynomial optimization

## Sum of Squares
Again we should ask linear in what?

m = [1 x x^2]

m^T Q m is a sum of squares polynomial if Q is positive semidefinite. The eigenvectors are the terms of the sum. 

This is the analog of $a^Tm$ being a linear parametrization of an arbitrary polynomial

Trick: you can find the optimal value of a polynomial by considering $p(x) + t$. You want to minimize t such that $p(x) + t$ stays positive.

Moments: This one always kind of confused me. Linear functionals s.t. if f(x) is sos that L[f] >= 0

# Complementarity Problems

xy = 0 constraints, which is another way of saying only one of x and y can be nonzero

# Mixed Integer

Techniques papers from the COAT slack

[https://pubsonline.informs.org/doi/10.1287/ited.7.2.153](https://pubsonline.informs.org/doi/10.1287/ited.7.2.153)

[https://link.springer.com/chapter/10.1007/11493853_27](https://link.springer.com/chapter/10.1007/11493853_27)

[https://dspace.mit.edu/handle/1721.1/96480](https://dspace.mit.edu/handle/1721.1/96480)

[https://link.springer.com/chapter/10.1007/11493853_27](https://link.springer.com/chapter/10.1007/11493853_27)

[https://docs.mosek.com/modeling-cookbook/index.html](https://docs.mosek.com/modeling-cookbook/index.html)
## Big-M
## Encoding boolean functions/relations
## Piecewise linear encodings
## Unrolling time

# Resources
- Stephen Boyd
- MIP school
- Operations research stack exchange
- DTU summer school
- [Advanced Optimization and Game Theory for Energy Systems](https://www.youtube.com/watch?v=Li5WZOeFeUQ&list=PLe7H9pun_r8YHoGv0TnYxUsgbj0xAJmMR&ab_channel=JalalKazempour)