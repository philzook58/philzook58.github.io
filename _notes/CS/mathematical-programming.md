---
layout: post
title: Mathematical Programming
tags: optimization
description: my notes about optimization
---
- [Optimization](#optimization)
    - [SAT vs SMT vs CSP vs MIP vs NLP](#sat-vs-smt-vs-csp-vs-mip-vs-nlp)
- [Linear Programming](#linear-programming)
  - [Tricks](#tricks)
    - [Encoding equality in terms of inequality](#encoding-equality-in-terms-of-inequality)
    - [Making the objective a single variable](#making-the-objective-a-single-variable)
    - [Absolute value encoding](#absolute-value-encoding)
    - [Sparsity Heuristic](#sparsity-heuristic)
    - [Minimax encoding](#minimax-encoding)
    - [Linear in _what_?](#linear-in-what)
    - [Polytope inclusion](#polytope-inclusion)
  - [Applications](#applications)
    - [Discrete Optimization Problems](#discrete-optimization-problems)
    - [Control](#control)
      - [Q Learning](#q-learning)
    - [PDEs](#pdes)
    - [Denoising](#denoising)
    - [Compressed sensing](#compressed-sensing)
    - [Inverse Problems](#inverse-problems)
    - [Optimal Transport](#optimal-transport)
    - [System Identification](#system-identification)
    - [Min Path](#min-path)
    - [Max flow](#max-flow)
    - [Polynomial Solutions](#polynomial-solutions)
    - [Fitting floating point polynomials](#fitting-floating-point-polynomials)
    - [Quantization](#quantization)
  - [Polyhedral Computation](#polyhedral-computation)
    - [Fourier Motzkin](#fourier-motzkin)
    - [Hrep Vrep](#hrep-vrep)
    - [Zonotopes](#zonotopes)
    - [Resources](#resources)
  - [Methods](#methods)
    - [Simplex](#simplex)
    - [Interior Point](#interior-point)
- [Convex Optimization](#convex-optimization)
- [Duality](#duality)
  - [Duals as Proof](#duals-as-proof)
  - [Geometrical Perspective](#geometrical-perspective)
  - [Lagrange Multipliers and Legendre Transformation](#lagrange-multipliers-and-legendre-transformation)
- [Quadratic Programming](#quadratic-programming)
- [Conic Programming](#conic-programming)
- [Semi-Infinite Programming](#semi-infinite-programming)
- [Semi definite programs](#semi-definite-programs)
  - [Tricks](#tricks-1)
  - [Applications](#applications-1)
  - [Sum of Squares](#sum-of-squares)
  - [Laserre hierachy](#laserre-hierachy)
- [Convex Optimization](#convex-optimization-1)
- [Mixed Integer](#mixed-integer)
  - [Big-M](#big-m)
  - [Encoding boolean functions/relations](#encoding-boolean-functionsrelations)
  - [Piecewise linear encodings](#piecewise-linear-encodings)
  - [Unrolling time](#unrolling-time)
- [Extended Mathematical Programming](#extended-mathematical-programming)
- [Stochastic programming](#stochastic-programming)
- [Robust Optimization](#robust-optimization)
- [Complementarity Problems](#complementarity-problems)
- [Parametric Programming](#parametric-programming)
- [Difference of Convex Programming](#difference-of-convex-programming)
- [Bilevel programming](#bilevel-programming)
  - [method 1 KKT condition](#method-1-kkt-condition)
  - [Duality](#duality-1)
- [Tools](#tools)
  - [NEOS server](#neos-server)
  - [COIN-OR](#coin-or)
  - [CLP](#clp)
  - [SCIP](#scip)
  - [JuMP](#jump)
  - [CVXPY](#cvxpy)
  - [PYOMO](#pyomo)
  - [YALMIP](#yalmip)
  - [Commercial](#commercial)
    - [Gams](#gams)
    - [Ampl](#ampl)
    - [Gurobi](#gurobi)
    - [CPLEX](#cplex)
    - [Mosek](#mosek)
    - [Highs](#highs)
    - [COPT](#copt)
- [Resources](#resources-1)

# Optimization

I should renamed this article to Mathematical Programming / Operations Research / maybe convex optimization. More generally, optimization also includes general non linear optimization. Things like gradient descent, genetic algorithms, interval stuff etc etc.

### SAT vs SMT vs CSP vs MIP vs NLP

When and why?
Hard to know.

# Linear Programming

$$ \min c^T x $$
$$ Ax \le b $$

## Tricks

### Encoding equality in terms of inequality

$$ Ax \le b $$ and Ax \ge b $$ gives an equality

### Making the objective a single variable

Make a new variable $$ t $$ and add constraint $$ t = c^T x $$. Now you can minimize $$ t $$ instead.

### Absolute value encoding

min \sum_i |c_i^T x|

You can create a new variable t_i for each absolute value term
replace with

min \sum_i t_i
\forall_i t_i <= c_i^T x <= t_i

### Sparsity Heuristic

Adding an absolute value regularization term $ \sum |c|$ has a tendency to for the c exactly to zero.
You can tune the amount of sparsity you want. Then you can also force the sparsity as a new problem or as new linear constraintst c = 0, and resolve without the regulairization to finetune.

- [Basis pursuit](https://en.wikipedia.org/wiki/Basis_pursuit)
- [LASSO](https://en.wikipedia.org/wiki/Lasso_(statistics))

### Minimax encoding

A similar feeling trick

min ( max_i c_i^T x)

create a _shared_ bound t

min t
\forall_i c_i^T <= t

Because minimizing t tries to push against these new constraints, t will end up being the maximum of them. The constraint correspond to this will be tight, whereas the others will be slack.
This trick does not generalize as much as one might naively hope. Nested optimization is often difficult. See bilevel optimization.

### Linear in _what_?

### Polytope inclusion

## Applications

[cvxpy examples](https://www.cvxpy.org/examples/index.html)

- least absolute value optimization
- Relaxations of discrete optimization problems
- Network flow
- how do strings hang
- Contact constraints

### Discrete Optimization Problems

If an optimizaion problem has a poly time algorithm, there's a decent chance it isn't so bad to embed in linear programming

### Control

- [cvxpy control demo](https://colab.research.google.com/github/cvxgrp/cvx_short_course/blob/master/intro/control.ipynb)
- [Categorical Combinators for Convex Optimization and Model Predictive Control using Cvxpy](https://www.philipzucker.com/categorical-combinators-for-convex-optimization-and-model-predictive-control-using-cvxpy/)
- [2D Robot Arm Inverse Kinematics using Mixed Integer Programming in Cvxpy](https://www.philipzucker.com/2d-robot-arm-inverse-kinematics-using-mixed-integer-programming-in-cvxpy/)
- [Boundcing a Ball with Mixed Integer Programming](https://www.philipzucker.com/bouncing-a-ball-with-mixed-integer-programming/)
- [Trajectory Optimization of a Pendulum with Mixed Integer Linear Programming](https://www.philipzucker.com/trajectory-optimization-of-a-pendulum-with-mixed-integer-linear-programming/)
- [Mixed Integer Programming & Quantization Error](https://www.philipzucker.com/mixed-integer-programming-quantization-error/)
- [Model Predictive Control of CartPole in OpenAI Gym using OSQP](https://www.philipzucker.com/model-predictive-control-of-cartpole-in-openai-gym-using-osqp/)
- [LQR with cvxpy](https://www.philipzucker.com/lqr-with-cvxpy/)
- [Flappy Bird as a MIP](https://www.philipzucker.com/flappy-bird-as-a-mixed-integer-program/)

#### Q Learning

[More Reinforcement Learning with cvxpy](https://www.philipzucker.com/more-reinforcement-learning-with-cvxpy/)
[Q learning with linear programming](https://www.philipzucker.com/q-learning-with-linear-programming-cvxpy-openai-gym-pendulum/)

### PDEs

You can encode some PDEs to mip to find the minimal energy ground state.
[XY model with MIP](https://www.philipzucker.com/solving-the-xy-model-using-mixed-integer-optimization-in-python/)
[Coulomb Gas as Mixed integer program](https://www.philipzucker.com/the-classical-coulomb-gas-as-a-mixed-integer-quadratic-program/)
[Solving the Ising model with MIP](https://www.philipzucker.com/solving-the-ising-model-using-a-mixed-integer-linear-program-solver-gurobi/)

### Denoising

Total variation reconstruction <https://en.wikipedia.org/wiki/Total_variation_denoising>

### Compressed sensing

<https://en.wikipedia.org/wiki/Compressed_sensing>

### Inverse Problems

<https://en.wikipedia.org/wiki/Inverse_problem>
Inverse problems are trying to determine stuff from observations.
In particular, you're trying to infer the systems of equations that define a system from different solutions of the system. The system of equations of a wave system or laplace system will include the shape of objects in the system

### Optimal Transport

Discrete optimal transports problems can be encoded as an LP. Optimal transports is an idea with a long history (Monge) and a lot of work (fields medals and such). Kind of curious.

Optimal transports is moving hunks of dirt from points A to points B. If these sites are discrete, you can encode how much went along each pathway and have a cost with that pathway associated with it's geometric distance.

### System Identification

<https://www.philipzucker.com/system-identification-of-a-pendulum-with-scikit-learn/>

### Min Path

```python
import cvxpy as cvx
edge = cvx.Variable((3,3), nonneg=True)
path = cvx.Variable((3,3), nonneg=True)

constraints = []
constraints += [path[i,j] >= edge[i,j]  for i in range(3) for j in range(3)]
constraints += [path[i,k] >= edge[i,j] + path[j,k] for i in range(3) for j in range(3) for k in range(3)]
constraints += [edge[0,1] == 1, edge[1,2] == 1] # Plus all non existent edges have weight inifinty

prob = cvx.Problem(cvx.Minimize(cvx.sum(path) + cvx.sum(edge)), constraints)
print(prob.solve())

```

Conversely, min-path algorithms can solve problems of this form.

### Max flow

<https://en.wikipedia.org/wiki/Maximum_flow_problem>

### Polynomial Solutions

### Fitting floating point polynomials

Floating point up to 32 bit is tractable via complete enumeration of the space.
You can design polynomial approximations that directly use the tabulation of true floating point result.
See Rlibm project.

### Quantization

## Polyhedral Computation

We have methods for really dominating polyhedra. You can answer a lot of difficult questions about them. However, linear programmig is cheap, polyhedral methods are expensive

[FORMALIZING THE FACE LATTICE OF POLYHEDRA](https://arxiv.org/pdf/2104.15021.pdf) in coq

The face lattice is a neat idea
[face lattice](https://en.wikipedia.org/wiki/Convex_polytope#The_face_lattice)
[Abstract polytope](https://en.wikipedia.org/wiki/Abstract_polytope)
[Steinitz's theorem](https://en.wikipedia.org/wiki/Steinitz%27s_theorem) algorithmi steinitz problem. Recognize face lattice of polytopes. <https://mathoverflow.net/questions/432636/determining-whether-a-lattice-is-the-face-lattice-of-a-polytope-np-hard-or-und>
[Polyhedral Combinatorics](https://en.wikipedia.org/wiki/Polyhedral_combinatorics)

[Hirsch Conjecture](https://en.wikipedia.org/wiki/Hirsch_conjecture)

Ziegler - Lectures on polytopes. 0-1 poltopes

Volume computation
Simplicial decomposition

### Fourier Motzkin

Fourier motzkin is conceptually simple. It is the inequality analog of gauss elimination, but much more computationally complex. Pick a variable x to project out of your equations. Isolate this variable. Because of minus signs, sometimes you'll have x less than, sometimes x greater than.
$$ x <= f_j(y) $$
$$ g_i(y) <= x $$

Now plug together the n <= inequalities, with the m >= inquealities to produce n*m inequalities that don't have x. This is a project set of inequalities for which if they are satsifiable, you can produce an x that is also satisfiable. To do so, find y. Find the maximum of $$ g(y) $$ and the minimum of the $$f(y)$$. Pick an arbitrary x between these bounds. $$ max_i g_i(y) <= x <= min_j f_j(y) $$

### Hrep Vrep

Polyhedra can be dually described as the convex hull of their vertices (Vrep) or the intersection of the halfspaces of their faces (Hrep). Both of these can be concretely represented by collections of vectors.
These different representations make different operations easy. Converting between them is hard in general. Some polytope only even have succinct representation in one rep vs the other. For example, a cube has 2*d faces, but 2^d vertices for dimension d.

convex union is easy in VRep, just take the union of the vertices (and cull the interior points?)

interesection is easy in Hrep, take both sets of half spaces

### Zonotopes

Zonotopes are the linear images of cubes. This is a special form of polyhedra that sometimes has nice properties

### Resources

[Fukuda lecture notes](http://www-oldurls.inf.ethz.ch/personal/fukudak/lect/pclect/notes2015/PolyComp2015.pdf)

## Methods

### Simplex

### Interior Point

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

## Duals as Proof

I can derive new inequality bounds by combining the rows of A. When you add together inequalities, you have to multiply by positive coefficients only, or you will flip the direction of the inequality. If I left multiply by a vector $latex l \ge  0$ I can derive new bounds from the assumption that you are in the polytope.  This is similar to deriving new _equations_ from sum of the rows of a matrix that occurs during Gaussian elimination.

$latex l^TAx \ge l^Tb$

How can we use that to find a bound on the objective. Well if we add the additional constraint that $latex A^T l = c$ then we derive the new bound $latex l^TAx = c^T x\ge l^Tb$. So by fiddling with the values of l, we may try to create better and better lower bounds on the objective function derived from the polytope constraints.

If I can exhibit both an $latex l^_$ and and $latex x_$ such that $latex c^T x = l^*^T b$ then I'm golden no matter how I cheated and killed to find them.

It is a remarkable fact that these vectors are in fact guaranteed to exist. That is the content of strong duality and Farkas Lemma.

Sometimes the dual is called a certificate of optimality. But we can also consider it to be a proof object. It is data that somehow encodes a particular kind of linear sum of inequalities proof.

## Geometrical Perspective

As I said above, each row of the matrix A corresponds to a half space.

More generally, any convex set can be considered the as the convex union of all it's points or dually as the intersections of all the half spaces that fully include the object.

Half spaces can be coordinatized as a normal vector l and an offset parameter r such that $latex \{ x | l^T x \ge r \}$.

Looking at only the extremal bits (the boundary), a convex set is the convex hull of it's boundary and the set is the envelope of it's extremal halfspaces (those that actually touch the set).

$latex \{ x | x \elem C \}$ $latex \{ (l ,b)| \forall x \in C, l^T x \ge b \cap \}$

$latex \{l | l \in C^_\}$    $latex \{x | \forall l \in C^_  \}$

In the affine geometry we're considering, these two things don't

The duality becomes much cleaner when we remove the offsets and work in projective geometry. Everything becomes homogenous coordinates and instead of talking about convex sets, we talk about conic sets.

We can recover the affine considerations by taking a slice of the cone z = 1. This is the standard way of going back and forth between homogenous coordinates and regular coordinates.

A Cone is a set that is closed under non-negative combinations of it's points. The dual cone is the set of all half spaces at the origin that fully contain the primal cone.

## Lagrange Multipliers and Legendre Transformation

# Quadratic Programming

# Conic Programming

# Semi-Infinite Programming

infintie number of constraints or variables

EAGO.jl <https://github.com/PSORLab/EAGO.jl> <https://psorlab.github.io/EAGO.jl/dev/semiinfinite/semiinfinite/>

# Semi definite programs

optimization over positive semidefinite matrices. Very powerful
<https://arxiv.org/abs/2202.12374> - iterate sdd to get sdp. sounds good
[quantum and sdp](https://twitter.com/jj_xyz/status/1501220764506337287?s=20&t=_9HZg1SjTUMm-W15rZhP5w)

## Tricks

Semidefinite kind of gets you multiplication

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

## Laserre hierachy

Adam sherali mention in linear programming? Probablistic moments.

We have a problem that involves x, y, and x*y but is otherwise linear. Suppose we introduce a variable called "xy", and the constraint `xy = x * y`. As a relaxation we can just forget the constraint. This is a pretty loose relaxation.

# Convex Optimization

More general solvers, are less specific.
Convex Sets
Convex Cones
Epigraphs
Geometric programming - I don't really know about this one
Barrier method

# Mixed Integer

## Big-M

## Encoding boolean functions/relations

Any boolean function/relation is a convex polytope subset of the hypercube + integer constraints.

## Piecewise linear encodings

[PiecewiseLinearOpt.jl](https://github.com/joehuchette/PiecewiseLinearOpt.jl) [paper](https://arxiv.org/abs/1708.00050)

## Unrolling time

[Products of Variables in Mixed Integer Programming Gurobi tutorial](https://www.youtube.com/watch?v=HS5HVCMORbo)
Mccormick relaxation

Techniques papers from the COAT slack

[https://pubsonline.informs.org/doi/10.1287/ited.7.2.153](https://pubsonline.informs.org/doi/10.1287/ited.7.2.153)

[https://link.springer.com/chapter/10.1007/11493853_27](https://link.springer.com/chapter/10.1007/11493853_27)

[https://dspace.mit.edu/handle/1721.1/96480](https://dspace.mit.edu/handle/1721.1/96480)

[https://link.springer.com/chapter/10.1007/11493853_27](https://link.springer.com/chapter/10.1007/11493853_27)

[https://docs.mosek.com/modeling-cookbook/index.html](https://docs.mosek.com/modeling-cookbook/index.html)

# Extended Mathematical Programming

[extended mathematical programming](https://en.wikipedia.org/wiki/Extended_Mathematical_Programming)

disjunctive programming

# Stochastic programming

<https://en.wikipedia.org/wiki/Stochastic_programming>
The parameters of the future stage program are unknown. You need to optimize with respect to their expectation

Determinisitc equivalent

statistical sampling / monte carlo

# Robust Optimization

# Complementarity Problems

xy = 0 constraints, which is another way of saying only one of x and y can be nonzero

Complementrarity Book

If you pick which variables are 0, what remains is a convex optimization problem. So there is sort of a layered thing going on.

# Parametric Programming

# Difference of Convex Programming

[difference of convex programming](https://twitter.com/caglar_ee/status/1568899044520378369?s=20&t=Ed04dBodGtW0kFSYL76bNQ)
<http://www.lita.univ-lorraine.fr/~lethi/index.php/dca.html>
<https://www.ceremade.dauphine.fr/~carlier/toland.pdf>

# Bilevel programming

[Review on Bilevel optimization](https://arxiv.org/pdf/1705.06270)
[Gentle and incomcplete introduction to bilevel optimization](http://www.optimization-online.org/DB_FILE/2021/06/8450.pdf)
[yalmip bilevel](https://yalmip.github.io/tutorial/bilevelprogramming/)

Bilevel programming is a natural idea of modelling nested optimization problems. They occur when you want to optimize given that someone else is optimizing
For example, suppose you want to optimize a trajectory for worst case error forces. You minimize a cost while errors are trying to maximize it.
Or the two problems can have unrelated objectives

[GAMS](https://www.gams.com/latest/docs/UG_EMP_Bilevel.html)

[Mathematical programming with equilibrium constraints](https://en.wikipedia.org/wiki/Mathematical_programming_with_equilibrium_constraints) a

[modeling bilevel programs in pyomo](https://www.osti.gov/servlets/purl/1526125)

Game Theory
Nash equilbirium

Follower leader problems
[interdiction problem](https://www.usna.edu/Users/math/traves/papers/interdiction.pdf)

[pyomo bilevel](https://cfwebprod.sandia.gov/cfdocs/CompResearch/docs/pyomo_bilevel_sandreport.pdf) deprecated?

```python
from pyomo.environ import *
from pyomo.bilevel import *
model = ConcreteModel()
model.x = Var(bounds=(1,2))
model.v = Var(bounds=(1,2))
model.sub = SubModel()
model.sub.y = Var(bounds=(1,2))
model.sub.w = Var(bounds=(-1,1))
model.o = Objective(expr=model.x + model.sub.y + model.v)
model.c = Constraint(expr=model.x + model.v >= 1.5)
model.sub.o = Objective(expr=model.x+model.sub.w, sense=maximize)
model.sub.c = Constraint(expr=model.sub.y + model.sub.w <= 2.5)
```

## method 1 KKT condition

Optimal points of the lower problem hav KKT conditions ~ gradient = 0. These are equality constraints. This turns it into a nonlinear optimization problem.
It is not entirely clear to me that any point that satisfies kkt conditions is necessarily a global optimum. That sounds ok... hmm

KKT conditions include complementarity conditions, converting into a complementarity problem. This can in turn perhaps be encoded into MIP. Or possibly you might end up with a system of polynomial equations which can be treated (at small scale) using homotopy continuation methods or other algebraic methods.

## Duality

You can reformulate to the dual problem. This will cause xy terms in the inner objective. Not awesweom

# Tools

## NEOS server

Online job submission to many solvers. Good place to find out about solvers
<https://neos-server.org/neos/>

## COIN-OR

## CLP

Free and very fast linear programming solver.

## SCIP

many parameters. Fuzz them?

## JuMP

## CVXPY

## PYOMO

## YALMIP

[yalmip](https://yalmip.github.io/) matlab toolbox for optimization. Lots of cool little things though. See tutorials for example

## Commercial

There's nothing wrong with wanting to make money off your hard work, but commercial solvers are less useful/interesting to me personally. They are annoying enough to even get free licences for.

### Gams

### Ampl

### Gurobi

### CPLEX

### Mosek

### Highs

<https://ergo-code.github.io/HiGHS/index.html>
Interesting. Rust, Julia, javascript bindings.
MIP solver.
Performance seems roughly competititive

### COPT

INteresting new performer
<https://www.shanshu.ai/copt>
LP, MIP, SOCP, SDP, convex QP and convex QCP
Non free

<https://github.com/oxfordcontrol>

- [Clarabel.rs](https://github.com/oxfordcontrol/Clarabel.rs) and julia version
- [Cosmo](https://github.com/oxfordcontrol/COSMO.jl)

[osqp](https://github.com/osqp/osqp) quadratic optimization solver

# Resources

- Stephen Boyd
- MIP school
- Operations research stack exchange
- DTU summer school
- [Advanced Optimization and Game Theory for Energy Systems](https://www.youtube.com/watch?v=Li5WZOeFeUQ&list=PLe7H9pun_r8YHoGv0TnYxUsgbj0xAJmMR&ab_channel=JalalKazempour)
- [Hans Mittlemann benchmarks](http://plato.asu.edu/bench.html) This was kind of causing some drama

[resotta opf](https://github.com/lanl-ansi/rosetta-opf) AC optimal power flow model
Power flow is a place where mathemtical optimization is pretty interesting

[Gekko](https://gekko.readthedocs.io/en/latest/quick_start.html)

cvxpygen

[Yet Another Math Programming Consultant](https://yetanothermathprogrammingconsultant.blogspot.com/)

[Max cut](https://twitter.com/parubin/status/1537815438368858114?s=20&t=Id3zoB1xCWLA5QQIrPNHVA)

<<<<<<< HEAD
<https://twitter.com/caglar_ee> ths guy is tweeting a ton f courses

[linear optimziation UW-madison](https://www.youtube.com/playlist?list=PLeO_PhASIA0Ot69TqANAnNxoykHGOQp2Y)

[integer optimization](https://www.youtube.com/playlist?list=PLeO_PhASIA0NlDNF9y-SsgVEYcvAMj2CY)

[intro to optimization](https://laurentlessard.com/teaching/524-intro-to-optimization/) in julia
