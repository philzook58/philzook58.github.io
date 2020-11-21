---
author: philzook58
comments: true
date: 2017-04-13 21:27:50+00:00
layout: post
link: https://www.philipzucker.com/chebyshev-polynomials/
slug: chebyshev-polynomials
title: Chebyshev Polynomials
wordpress_id: 684
---

Chebyshev polynomials are really cool.

No please. Don't leave. I'm so lonely.

They really are. I remember them coming up a lot during my Gilbert Strang phase (his numerical computing course online is really awesome). When in doubt use Chebyshev polynomials.

They have a lot of great properties. A lot of special functions are just a bunch of random garbage.

The key to Chebyshev polynomials is that they are really $ \cos $ in disguise. and they inherit a ton of properties just from that. $ \cos $ is a very special function.

$ T_n(\cos(\theta)=\cos(n\theta))$

What this says is that if you transformed  the domain [-1,1] using $ x=\cos(\theta) $, then the Chebyshev polynomials are just cosines. A couple of properties fall out of this.

First, the equioscillation property. One thing that defines chebyshev polynomials is that they are polynomials with the minimum maximum values on the domain, i.e. they oscillate between -1 and 1. This is why they are good for function approximation. Using them tends to make the approximation error have a minimum maximum value over the interval. Other polynomials of the same degree overshoot the bounds.

This is not surprising from the cosine perspective.

An equally spaced grid is the best one in a periodic domain. This domain transformation transforms the equally spaced grid $ \theta_n = n/2\pi N$ to the chebyshev points $ x_n = \cos(n/ 2\piN)$. It is somewhat surprising that these are actually much better points to sample functions at rather than the equally spaced points.

A fast $ n \ln n$ transform between the chebyshev coefficients and the sampled point values can be achieved using the discrete cosine transform. The discrete cosine transform takes an expansion in cosines to samples on the equally spaced grid and again the chebyshev functions are just cosines in disguise.

They inherit orthonormality from the orthonormality of cosines.

An advantage that chebyshev functions have over cosines is that they are polynomials. This makes them easy to manipulate and compute. The correct way to evaluate a Chebyshev series is using the recurrence.

$ T_n(x)=2xT_{n-1}(x)-T_{n-2}(x)$

Once you've sampled a function into Chebyshev form, it is simple to differentiate, integrate, multiply, and add functions. Composition of functions may be a bit harder. There is the very interesting relation that $ T_n(T_m(x))=T_{nm}(x)$, but it is not clear to me that there is an easy way to find a relation $T_n(a+b)$ in order to evaluate the composition of full Chebyshev series efficiently.

For differentiation and integration it is important to remember the $ \sin$ factor that occurs due to the change of domain from the unit circle to the unit interval.

Transformation between the samples at Chebyshev points and the polynomial coefficients can be achieved using a DCT.

There are two sets of Chebyshev points, one for roots of $ T_n$ one for the extrema.

The Cosine Series works with an implicit even periodic extension of the function you want to approximate. This is why it can work better than approximating a non periodic function with the Fourier series, where the implicit periodic version will have discontinuities.

Root finding becomes possible.

scipy has some solid chebyshev capabilities.

It surprises me that Haskell does not have an appropriate translation of chebfun as far as I can find. Chebfun is such a functional kind of thing, a beautiful programming pattern.

https://hackage.haskell.org/package/math-functions

This library has some basic chebyshev capabilities

I'd like to take moment here to comment how important the vector type is in Haskell. It is not mainstream in the sense that any Haskell tutorial mentions it as I recall, but it gives you access into the world of c-like arrays (which is ugly and unhaskelly I guess).






