---
author: philzook58
comments: true
date: 2018-05-01 17:31:42+00:00
layout: post
link: https://www.philipzucker.com/?p=1061
published: false
slug: SAT Cartpole
title: SAT Cartpole
wordpress_id: 1061
---

The basic idea pump here is that Model Checking is a related activity to Control. Model Checking is about proving properties of discrete dynamical systems. Control is usually about finding ways to make continuous dynamical systems do what you want (hopefully with a proof that such a scheme will always work). In the context of model checking, I feel like the problem is usually phrased as a given model with no control parameters. It is checking not design. But I bet people know and think about ways of using model checking to do design.

Also see SatPlan. Motion Planning is again another flavor of control. (Usually a focus on pure geometry rather than dynamics, but its all kind of the same shit)

So I was thinking about the puzzle where you need to do weighings to figure out which coins are heavy or whatever. It needs to work forall possible actual weightings and you are allowed to change your decision based on the information you've previously gained. I think the forall actual states needs to go in the interior of the problem. Then alternating forall knowledge states, the exists a decision. And constrain the knowledge states to be consistent with the actual state. Tough prob.

To have something derive a strategy for all situations gets translated to There Exists a strategy Forall possible realities. This is kind of bad news for using a SAT solver. I haven't been able to figure out how to compress this into a SAT instance and I have some reason to believe I can't.

One can remove a forall by conjoining formulas with both possibilities and remove there exists by ORing both possibilities for that variable.

There is an extended class of solvers called QBF (Quantified Boolean Formula solvers). There is also something called the Polynomial Hierarchy which extends NP (search problems. If you find one you've done it. Proving There Exists with an example) and coNP (showing something can't happen. Proving ForAll) to alternating foralls and exists.

An interesting idea is to use a SAT solver to find a boolean parametrized function (controller) that does what you want. Also interesting is how wicked fast something like that could be run, as asynchronous logic circuit in fpga. One could use neural network inspired structures perhaps, like with a hierarchy of convolutions and such. The most obvious feeling parametrization would be some kind of sum of products form. Kind of feels like dotting a weight vector w on the input x. This also feels like polynomial fitting.

I think that BDDs might still have a handle on this style of problem though. The condition of reaching and staying at a control point is probably expressible in LTL. The stochastic dynamics can be expressed in an NDA by conjoining all of the possibilities of external forces in T(x,x'). One would think some kind of scaled ordering of the variables might help, since little details don't affect the big details much unless the system is very sensitive (chaotic?).

This does seem ass backwards to use SAT and mixed integer or exact nonlinear solvers feel more appropriate. But an interesting mental exercise. Hey, who know, maybe it'll even work ok.

It isn't clear to me whether one should encode positions using fixed point, or one-hot booleans. Will fixed-point confuse the solver? One could use some kind of multiscale scheme.

We could use Z3 with bitvectors. Another advantage of this approach is that one can literally use the bit depth that your microcontroller actually has. For that matter, we can cosimulate microcontroller and cartpole in sbv and have it derive the code

If we fix the initial conditions, then we do get to remove the forall worrying about all initial conditions.

If we suggest a controller, we can use SAT to search for a counterexample to it working.

Bounded Model Checking unrolls the transition relation for a number of steps. This is like how trajectory optimization unrolls the dynamics for a number of steps.

Lyapunov style proofs use a decreasing function. These have the feel of invariant based proofs

$latex \phi(x') < \phi(x) \land T(x,x') $ sort of has a similar feel to

$latex \phi(x) \land T(x,x') \implies \phi(x') $
