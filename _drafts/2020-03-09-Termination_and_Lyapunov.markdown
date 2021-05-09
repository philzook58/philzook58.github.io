---
author: philzook58
comments: true
date: 2020-03-09 18:47:25+00:00
layout: post
link: https://www.philipzucker.com/?p=2685
published: false
slug: Termination and Lyapunov Functions
title: Termination and Lyapunov Functions
wordpress_id: 2685
---

2021- 02

Coq and termination
Accessibility relations, Sam's paper
Bove-Capretta method - a Defunctionalization of the Acc method?
Adding an accessibility parameter - delays the requirement of proof to when it receives this




2020-12-07

Polynomial interpetations - each function symbol goes to some polynomial. variable stay variables.
f(g(x,y)) ->   yada yada
If you bound you coefficents to integers and small, the nonlinearity of the coefficients from f and g aren't persay a problem

RPO. recsurive path orderings.

String rewriting termination. The simpler model.
abc -> cdf
assign each guy to an nonegative integer.
a + b + c > c + d + f.

This one is actually an ILP.

This is polynomial interpetation where concat/cons symbol has intepretation of plus and each constant symbol has interpetation of a number.

http://www.cs.tau.ac.il/~nachumd/papers/termination.pdf dershowitz termination review 1987

The obviously terminating stuff always decreases
Doesn't always decrease, but clearly we lose 3 aaa to make a c but only gain 2 a from a c. We're losing net a every time we make a step.
c -> aa
aaa -> c

strategy : build string model of finite depth term rewriting system. See if it works.
build ground terms instantiation on term rewrite system. Constrain somehow
Possibly try to encode "good" thing in objective function.
Find failure. iterate.
This is a cegis.



2020-03-09

A Harmonic Oscillator. Prove that it is stable. Build lyapunov function. Can do with SDP. V >= 0, st. $latex \frac{d}{dt} xVx <= 0$. Or better yet $latex \frac{d}{dt} xVx <= \eps$ or $latex \frac{d}{dt} xVx <= eps (x V x)$.

Also could consider breaking up space into polyhedral regions (quadrants for example. Find a piecewise linear lyapunov function.

Another interesting problem is to prove escape from a region. Prove that osciallator eventually escapes x>=1. No prob. We also get a bound on the time it takes.  V(x) = cx. dot V = c xdt = c A x <= eps forall x >= 1.

min eps,   forall x. c A x - eps <= lam (x - 1)  ... this is not possible. lam needs to become a positive polynomial. No, it is possible if lam = cA xhat  and eps <= lam.

An interesting discrete analog of this system would be a swapper. x0 >= 1 implies x0' = x1, x1' = x2, x2' = x3, x3' = x0-1. The minus 1 gives us a small decay term.

For a string rewriting system, the simplest thing is just look at some kind of count on the symbols. Maybe with some weighting. It may be that you are always decreasing. If just count doesn't work, you can try 2-grams or other features/combos. This feels something like a sherali-adams 

For term rewriting, we could try to ignore the parse structure and use the count as string rewrite as above. Polynomial interpetation appears to want to interpret a term that is applied as a polynomial. This seems like it would create difficult nonlinear constraints for both verification and synthesis. Although if you constrain each polynomial to be bounded integers, it may make sense to pound them into a sat solver. Ok if each intepretation is only linear, then the combined would still be linear for verification.

AProve [http://aprove.informatik.rwth-aachen.de/index.asp?subform=home.html](http://aprove.informatik.rwth-aachen.de/index.asp?subform=home.html) aachen

TTT innsbruck [http://eptcs.web.cse.unsw.edu.au/paper.cgi?ThEdu19.4](http://eptcs.web.cse.unsw.edu.au/paper.cgi?ThEdu19.4)

Integer and Polynomial Programs. This means something rather different from integer programming. The idea is that all variables are integer, but you still have a notion of time. Guarded transitions. It seems likely I could compile this into an integer program. Reify inequality conditions.

Cegar loop. Can run program to get a bunch of traces. Use traces and find a decreasing function on all traces.

[https://link.springer.com/chapter/10.1007/978-3-540-72788-0_33](https://link.springer.com/chapter/10.1007/978-3-540-72788-0_33) SAT solving for temrination checking. It does appear they slam nonlinear arithmetic problems into sat solver.s

Dependency pair? What is this. People seem to think it is very important

The control community has similar questions and similar yet different appproaches. They often want continuous state.

[https://github.com/blegat/SwitchOnSafety.jl](https://github.com/blegat/SwitchOnSafety.jl)

[https://github.com/blegat/HybridSystems.jl](https://github.com/blegat/HybridSystems.jl)

SpaceEx. Platzer's stuff.  JuliaReach

Barrier functions. I think the idea is the you put a function that is diverging at the region you're worried about. If you can guarantee that this function is not diverging. 

Sum of Squares certificates. Describing sets as sublevel sets.

The S-Procedure. I think this is that you can relax all inequalities using your assumptions $latex  f(x) >=0 implies g(x) >=0$ then $latex g(x) >= \lambda f(x)$ and $latex \lambda >= 0 $ is sufficient. Sometimes it is necessary I think.

Hybrid Systems. Piecewise affine systems. 

Reachability. We want to figure out how to rewrite one equation into another. Building an A* style lower bound distance could be quite helpful. A lower bound cost to get to some position. In terms of a control objective function S(x,x'), V(x,x'). In a small finite graph this could be computed. But suppose we didn't have enough flexibility. Finite graph, linear function of the features.

Ok. Some things. My concern about nonlinearity for multiply composed functions. 1. you might interpet some things differently (as fixed polynomial interpretation). Makes sense for constructors and data structures, where we have some reasonable suggestions. Looking at HEADs seems to matter a lot / give important over approximations of the behavior of the system. integer transition system. We can pattern match on fixed integers. f(x, 1) = yada.   f(x,y) -> f(y+1,x).  This we can do with guards.  f(x) | x > 7 -> g(x + 7).  f ~ 1 + a x + bx^2 + ... and so for g. Then f(x) >= g(x) + lam guard is lyapunov condition. We want struct inequality, that is the point of the integer nature of the system.  f(x) | x < 7 -> f(x**2 -  ) 

sum(n, acc) -> sum(n - 1, acc+n)

