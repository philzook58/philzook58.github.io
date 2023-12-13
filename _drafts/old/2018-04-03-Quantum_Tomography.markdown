---
author: philzook58
comments: true
date: 2018-04-03 17:57:04+00:00
layout: post
link: https://www.philipzucker.com/?p=1032
published: false
slug: Quantum Tomography
title: Quantum Tomography
wordpress_id: 1032
---

Inequality constraints are treated by a barrier method. You put a barrier into the objective function so that it won't want to violate the constraints.

It turns out that a very good one is a logarithmic barrier.

One acceptable convex inequality constraint is that a matrix should stay positive semi definite. Roughly that means it needs to have all positive eigenvalues (Or that may be exactly what that means. I'm hedging my bets against some nasty corner case.).

The determinant of a matrix is a function that heads to zero as any eigenvalue goes to zero.

The determinant is efficiently computable via matrix decomposition, usually LU (aka Gaussian elimination).



Density matrix are symmettric positive semidefinite matrices that trace out to 1. The trace being 1 is a linear constraint and no problem. Being positive semidefinite is also no problem.

Hence a fitting procedure from classical measurements to a density matrix is a tractable.
