---
author: philzook58
comments: true
date: 2020-09-08 15:14:32+00:00
layout: post
link: https://www.philipzucker.com/?p=2844
published: false
slug: Abstract Domains for Real Functions
title: Abstract Domains for Real Functions
wordpress_id: 2844
---




Upper lower bound functions







Interval added to polynomial







Intervals on the coefficients







Constraining derivatives is different. We lose something on integration.







Solving the laplace equation







Turning iteration equalities into inclusions (Nielson book)







[https://www.cl.cam.ac.uk/~lp15/papers/Arith/](https://www.cl.cam.ac.uk/~lp15/papers/Arith/) metitarski. Get rid of strange functions by using rigourous polynomial/rational over/under approximations. Otherwise fairly standard resolution proving. + somehow using z3 to prune irrelevant crap







Taking PyRes and boosting it with z3, sympy, cvxpy sounds good







[https://blegat.github.io/publications/](https://blegat.github.io/publications/) Set programming thesis. Sets are a complex object kind of like functions







[https://github.com/SimonRohou/tubex-lib](https://github.com/SimonRohou/tubex-lib) Tubes. Here they implements functions as tubes. Basically a function is a region in 2D space. where every t is covered. A list of times [] and a list of intervals []. The integrals is easy to estimate precisely. This is a realitvely strahgtofeard persepctive. It's like the difference between polynomial methods for functions and just sampling persepctive, spectral vs finite difference







[http://benensta.github.io/pyIbex/](http://benensta.github.io/pyIbex/) [https://www.ensta-bretagne.fr/jaulin/iamooc.html](https://www.ensta-bretagne.fr/jaulin/iamooc.html)







[https://github.com/JuliaReach/ReachabilityAnalysis.jl](https://github.com/JuliaReach/ReachabilityAnalysis.jl) Lots of stuff to dig into here. Many references.







Equations that aren't equations. $latex x = \int \dot{x}dt$. We can turn this into iteration  $latex x_{n+1} = \int \dot{x}{n}dt$ or we can turn this into an inequation $latex x \subset \int \dot{x}dt$. 









