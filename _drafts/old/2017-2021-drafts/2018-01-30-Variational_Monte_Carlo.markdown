---
author: philzook58
comments: true
date: 2018-01-30 16:36:48+00:00
layout: post
link: https://www.philipzucker.com/?p=713
published: false
slug: Variational Monte Carlo
title: Variational Monte Carlo
wordpress_id: 713
---

[
](http://www.philipzucker.com/wp-content/uploads/2017/05/IMG_0262.jpg)The core of Monte Carlo is numerical style problems is replacing

Sums -> Expectation Values

And then the expectation values can be computed using a sampling procedure

This is a way of doing integration

A very neat aspect of the monte carlo methods is that it has an internal estimate of the error. The variance of your samples can be used to give an estimate of the error (assuming things are going right enough, no systematic problems).

The variational method requires the integration of many variables.

The variational method does not necessarily involve the optimization of parameters to lower the energy as much as possible, but often does.

The artistry and physical intuition requirements of the variational method are high. The proposed wavefunction must be capable of expressing the physics.

Some properties required are boundary conditions, identical particle symmetry or antisymmetry, cusp conditions at singularities of Hamiltonians.

Sample from the distribution $latex |\psi|^2$ calculate the expectation of $latex \psi^{-1}H\psi$.

$latex E[\psi^{-1}H\psi ]=\int|\psi|^2 * \psi^{-1}H\psi =  \int\psi^\dagger H\psi $

Dividing by $latex \psi$ feels really weird.

Presumably you'll calculate any derivatives involved in H analytically. You only need to real part because the complex parts should cancel giving a real energy.

The Slater Determinant is an important starting point. This is the wavefunction of noninteracting electrons. You can compute determinants (relatively) fast numerically using LU decomposition (Gaussian Elimination). Numpy will do it for you





For Monte Carlo Calculations what can be our benchmarks:

Single Particle problems

Positronium

Helium

Jellium / Homogenous Electron Gas

Gaussian Field Theory

Perturbative Regime - Weak Interaction






