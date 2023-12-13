---
author: philzook58
comments: true
date: 2015-12-22 20:52:19+00:00
layout: post
link: https://www.philipzucker.com/?p=342
published: false
slug: i epsilon games
title: i epsilon games
wordpress_id: 342
---

A classic trick is to approach the wave equation as if it were the laplace equation in imaginary time. The boundary conditions are specified by a pole prescription in fourier space using inifinitesimal $latex i \epsilon$

which tell you how to close your contour integral. This leads to the retarded, advanced, and feynman propagators and is one of the main mathemitcal distinctions between all the various green's functions. $latex i \epsilon$ games are subtle, because they are dirty (but ultimately useful) tricks to achieve other conceptually clearer operations like taking the real part or setting boundary conditions.

When you transition over to an infinite domain you can do some very strange things. On a finite lattice you can't squirm your way out, so it can be very clarifying.

One way of thinking about the $latex i \epsilon$ is that it introduces a vanishingly small decay or dissipation into an equation that ordinarily has none. Dissipation is a thing that is one way in time, so a dissipatory term naturally selects the forward direction of time or equivalently the boundary condition for the problem, either a inital value problem (retarded) or final value problem (advanced) or something that is kind of a mix (feynman).

In a finite periodic lattice (which is what we're implicitly working on if we use the Fourier transform, discrete or otherwise), the idea is to insert enough dissipation such that the wave propagating out of a source cannot wrap around in time or in space, which would be unphysical. In other words, we want the solution to decay as $latex e^{-t/T}$ or $latex e^{-x/L}$. The larger we make our box, the less of an effect this has, and in the infinite case is almost completely negligible. Another way of working with finite domains that you really want to be infinite is to insert an absorbing layer (sometimes called a perfectly matched layer in some contexts) at the edges. This is sort of the same thing except we're distributing the dissipation everywhere and so now we have no edges, leading to simpler more translationally homogenous equations that are solvable using the FFT. And the FFT is awesome. If your algorithm uses it, you've already won.
