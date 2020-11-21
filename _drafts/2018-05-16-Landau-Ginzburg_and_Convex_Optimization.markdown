---
author: philzook58
comments: true
date: 2018-05-16 19:32:46+00:00
layout: post
link: https://www.philipzucker.com/?p=1038
published: false
slug: Landau-Ginzburg and Convex Optimization
title: Landau-Ginzburg and Convex Optimization
wordpress_id: 1038
---

# Convex Landau Ginzburg

x = np.linspace(0,1,100).reshape((-1,1))
y = np.linspace(0,1,100).reshape((1,-1))

row = np.zeros(100)
row[0] = -2
row[1] = 1
col = row
K = np.toeplitz(row, col)
K2 = np.kron(np.eye(100), K) + np.kron(K, np.eye(100))

def V(phi):
a = 1 # The setpoint of the field
V1 = (phi[:,0] - a) #(phi - a)**2
V2 = -(phi[:,0] + a)
V3 = (phi[:,1] - a) #(phi - a)**2
V4 = -(phi[:,1] + a)
V5 = 0 # give slight slope for degenracy breaking
return np.max(V1, V2, V3, V4, V5)

min (del phi**2 + V)
V > V1
V > V2
.. etc

It is a QP.

Because we do not penalize the hump in the middle, it may spend more time in there than necessary, vortices will tend to delocalize. But sharps corners tend to collect solutions.

Using abs(del phi) it is an lp

min K x + Ky + V

s.t.

del phi < K

del phi > -K

Can either use linear approximations or ... Maybe you can't use LP for norm? It is convex though. Or tesselated norm approximating circles (polygons). Or l1, which does break rotational symmetry.

nonlinear sigma model -> Quadratic constraint QP. if we relax the equality to inequality. It is a reasonable heurstic.

Nonlinear permittivty model -- applications to magnetic problems? two options, f(del phi) where f is convex or del phi dot eps(del phi) which is more correct I believe? (Energy is actually H dot B when you get down to it.. or is it \int H dB). Similarly I think that a diode network is convex.

So there are options. What about Chern-Simons, Yang Mills? Do these have an interesting convex relaxation?
Navier Stokes?
Other nonlinear field theories?

XY model. The cuteness of the XY model lies in the MANY minima. That leads me to think there isn't much hope there. One could restrict to 0 to 2 pi. But the potential ias still almost maximally nonconvex. Ok. But again, relaxing the xy model to enclose the bulk of the circle rather than just the rim gives you the lndau-gnizburg equation with infinite walls. QCQP

Approximation of electron specturm with abs. Useful in bosonization. Or the 2d wedge cone in the 2d extensions.

Quantization: Maybe this is useful. However quantum must consider ALL minima, not just the global minima, Hence the convex relaxation is taking the approximation that the other minima are dominated. Quantum is forall (exhaustive search, universal), classical is exists (existential, search).

H = (H0, V)

An extension to a larger class of lie groups

Udag U - I = 0

Relax to Udag U - I < 0

Also may want U > 0 as an approximation of the S part of SU(N).

This is either a matrix inequality or an elementwise inequality.

This is an extension of the idea of taking e^itheta to the filled in unit circle. And of taking the unit ball for the nonlinzar sigma.

Consider Lattice Yang Mills. The Hamiltonian consists of loop terms for every face $latex trUUUU$. This might be a posynomial under sufficient restrictions which would suggest the methods of geometric programming. This is a stretch. The basic trick of geometric programming is to rewrite variables as exponential of new variables, which does feel physicsy, converting from the U form to the A (vector potential) form of the problem. It would be nice to come up with some convex relaxation that is useful.

Consider Chern Simons (Not really very good lattice versions).

Supposing that a LP ends up on a corner, We can write down the steepest descent approximation to the problem.

Ax >= b will have exactly N constraints satisfied. Use this subset as a basis trasnfomation

s = Ax-b

e^(-cs)dx, s>0

The solution is

e^{-cA^{-1}b}/  (detA)/\prod_i (A^{-1}c)_i

Maybe using ordinary steepest descent with gaussians on Barrier method will work.

Summarize all the inequality constraints into a single barrier function $latex B = \sum_i \ln (\phi_i) $. Perform optimization of H +tB. The parameter t is sort of a smoothing parameter. Once you find the optimumm, use the smooth constraint steepest descent method. Put only the linear approximation of H in the exponent and use the hessian of the Barrier function to compute the appropriate volume. But this is under the assumption that we really are smashing into the barrier?



Now if there is a degeneracy, we need to count that separate. And degeneracy is exactly the special case we will shoot for since it is closest to the nonconvex problem.

In a degenerate situation, we need to compute the volume of the object that is degenerate. This is apparently a hard problem (if one assumes an oracle model for set membership, which is questionable we do have the choice of introspective power)? Does this suggest a quantum computer would be good at this problem? Maybe it isn't as bad as I fear, since the kinetic energy term could break degeneracies.

For a smooth constraint getting saturated, we need to transform the coordinates perpendicular to the normal and integrate the spheres surroundign the gradient of the constraint.



Another thought: rho_2 is low rank for superconductor or low rank plus diagonal (correspond to free electrons). Perhaps using the l1 heurstic might make this problem more tractable. Standard Trace and positive semidefintie constraint hold since a density matrix. Antisymmettry is treatable as a linear constraint. There is something off here. I can't remeber what the problem is with this approach.



Another interesting theory is |phi_i - phi_{i+1}| < eps. Sort of like a rope of chain links that are free to move until they contact their neighbor. Should act approximately like the more ordinary |\grad\phi|^2

Why does physics use so many quadratic forms?



 	
  1. They are solvable and manipulable. We choose to use easy to use models.

 	
  2. We choose to look at cases where physics is smooth and continuous, therefore we can approximate functions locally to quadratic forms. Local approximations might be very good to across huge scales.

 	
  3. God prefers them.


But there is a saying by Rockefellar that the big barrier between solubility and insolubility is not linear to nonlinear, but from convex to non-convex.

So what pieces of physics could benefit from this?

Already contact physics uses convex optimization type things. The ability to add inequality constraints is useful to avoid going into walls. It is one perspective on how collision in physics engines is treated.

But we can also consider convex Hamiltonians and Lagrangians.

For classical nonlinear field theory, there are a couple of interesting examples. Permittivity is fairly nonlinear in physically reasonable situations. The Landau-Ginzburg equation can be relaxed to use the convex hull of the quartic potential and that may give some interesting results. This might reflect the situation at the critical point, where the bottom of the well is about to invert into the Mexican hat. What it does is allows the field to be happy at the zero value so it can't get all tangled up. (The tangling is part of what makes it all interesting though. The inability of the field to go to zero because of the energetic barrier is what makes supercurrents persist.)

I conjecture that for statistical physics and maybe quantum physics, convex Lagrangian are basically ones where steepest descent should work pretty well. There are no local minima. The quantum case is more questionable, since now we're really talking stationary phase, and maxima and stationary points also exist. It might all still be ok. Convex functions can't have stationary points I don.t think.



Here's another interesting example. The classical Ising model can be formulated as a mixed integer linear program. Define $latex q_{ij} = s_i \and s_j$ where all variables are binary. Then add constraints .

The XOR that appears from spin alignment (aligned is a different energy than unaligned) can be done with $latex x_i + x_j - 2 x_i \cdot x_j$ .

Similarly, the coulomb gas is a natural mixed integer program. Imagine a network of charges that are constrained to be integers $latex \in {-100,100}$.

There will be an interaction energy = $latex \sum V(x_i-x_j) Q_i Q_j$ and an external potential $latex \sum U(x_i)Q_i $

Then again using this squaring trick you can replace the whole thing with a linear program.

Wait. No you can't. Not exactly the same anyhow. Maybe you could introduce a binary exapnsion for Q and a binary expansions for QQ?

The integer constraint is sufficiently nonlinear that you can simulate squares, or really you don't actually need squares.

One wonders how much it hurts to remove the integer constraint?

During a branch and bound or cutting plane algorithm, instead of selecting the best branch, one should sum the result of both branches.

How well does this work for 1D and 2D ising models, for which we have exact solutions?

How much does removing the integer restriction hurt?

One wonders, the coulomb gas is intimately connected to the XY-model. Does this give a leg into that?




