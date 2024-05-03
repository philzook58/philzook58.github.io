---
author: philzook58
comments: true
date: 2018-01-30 15:14:36+00:00
layout: post
link: https://www.philipzucker.com/?p=970
published: false
slug: Simulating Fluids
title: Simulating Fluids
wordpress_id: 970
---

3/21
Lattice boltzmann
https://news.ycombinator.com/item?id=26610826
There was a nice julia post


jan/18

**Meshing of Navier Stokes**

CFL conditions

HyperDiffusion

Choice of face functions vs cell functions. Finite Volume method,

discretize

https://benedikt-bitterli.me/gpu-fluid.html



**Particle based methods (meshfree)**

particle in cell

interpolate functions like pressure and density using sampled values combined with interpolating functions.

$latex \phi(x)=\sum_p \phi_p S(x-x_p)$

Where in the hell are you going to get an analysis from?

The distinction between FLIP and others is subtle. Choice of updating V and whatnot.

Alternate advection (the fluid flow) and the force

Use movement of particles for the advection step.

newtype Particle = Particle {position:: V3, velocity:: V3, mass :: Double, color :: Color }

xstep :: [Particle]-> [Particle]

interpolate :: [Particle] -> Field

summarize :: [Particle] -> QuadTree

interpolate' :: QuadTree -> Field

type Position = V3

type Force = V3

type Field = Position -> Force





I would be inclined to use adiabatic pressure volume relation

Projection to incompressible velocity field: Find Divergence of interpolated V and then solve potential equation and add result to V.



Lattice Boltzmann

https://physics.weber.edu/schroeder/fluids/




