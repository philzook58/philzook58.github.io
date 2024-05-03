---
author: philzook58
comments: true
date: 2018-09-26 18:14:08+00:00
layout: post
link: https://www.philipzucker.com/?p=1311
published: false
slug: Vector Fields
title: Vector Fields
wordpress_id: 1311
---

A vector field something that gives a vector at every point in space.

The most naive

These two things even though they look the same, we should keep them seperate

data R3 = R3 Double Double Double

data V3 = V3 Double Double Double

type VField = R3 -> V3

for example

monopole :: VField

monopole (R3 x y z) = V3 (x /  r^3) (y /  r^3) (z /  r^3) where r = sqrt (x*x + y*y + z*z)

Straightforward enough. But there are more advanced ways to go about this. What if we wanted to go to polar coordinates

p2c :: Polar -> Cartesian

p2c (Polar r theta) = Cartesian (r * cos theta) (r * sin theta)

c2p :: Cartesian -> Polar

c2p (Cartesian x y) = Polar (sqrt (x *x + y * y)) (arctan2 y x)



Then

monopoleP :: Polar -> V3

monopoleP = monopole . p2c

However V has not changed at all.  V is still represented in the cartesian basis. The types are not protecting us.



A haskell ray tracer of a black hole

https://flannelhead.github.io/posts/2016-03-11-blackstar.html

There is an alternative description of vector fields as differential operators. One that takes a directional derivative at every point of a scalar field. Writing a differentiable function as (~>)

https://en.wikipedia.org/wiki/Differentiable_manifold



type VField = (R3 ~> Double) -> (R3 ~> Double)

c2p :: Cartesian ~> Polar

Now it is more clear how to transform the vector into a new basis

To get out components, apply the coordinate function

x :: R3 ~> Double

x (R3 x y z) = x

v :: VField

vx

vx = v x



vx is analogous to the previous

xcomp :: V3 -> Double

xcomp (V3 x y z) = x





type OneFormField = VField -> Double



The metric. There are questions here. Do we have to peel into the structure of ~>?

distance :: (R3, R3) -> Double

type MetricField = (R3 ~> Double, R3 ~> Double) -> R3 ~> Double



Another thing to consider is paths.

Double -> R3

and differentiable paths

Double ~> R3



Parallel Transport

Atlases - Regions of validity + Mappings between atlases. Sphere mapping

Exterior Calculus - Green's Theorem. The d operator.

first attempt

d :: (R3 ~> Double) -> (OneFormField) = (R3 ~> Double) -> (VField -> Double) = (R3 ~> Double) -> (((R3 ~> Double) -> (R3 ~> Double)) -> Double)

exteriorProduct.

length, volume

wedge :: (OneFormField, OneFormField) -> (VectorField, VectorField) -> Double







How does this jive with discrete characterization of vector fields.

[(R3, V3)] -- labelled point set. This could be interpretted as a sampling

consider Conal Elliott's semantics of FRP

Set (R3, Double) -- sampled function

[(Double, R3)] -- sampled path.

We may try to reconstruct a continuum version via linear interpolation or another interpolation scheme (polynomial perhaps). Using chebfun style, these conversion might not be all that lossy.



How to integrate vectors? There is no automatic integration to my knowledge.




