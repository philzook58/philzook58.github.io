---
author: philzook58
comments: true
date: 2016-10-21 14:52:47+00:00
layout: post
link: https://www.philipzucker.com/band-theory-mobius-strip/
slug: band-theory-mobius-strip
title: Band Theory on a Mobius Strip
wordpress_id: 528
---

I've been toying with a slightly interesting twist on band theory.

If we put a chain on a circle, the usual band with nearest neighbor tunneling is

$ E(k)=t \cos (k)$

Next nearest neighbor tunneling makes terms in the dispersion like cos(2k) that are more oscillatory.

You can dimerize to make the unit cell twice as large. That will cut the Brillouin zone in two and stack the original single band into two bands.

But what if we allow tunneling diametrically across the circle? Then the oscillations are so swift that a new interpretation opens up. If we consider the diametrically opposed positions to be the two components of a spinor, sort of we divide the circle size L in two. In k-space, this means our discretization of k is twice as coarse. In particular we split into antisymmetric and symmetric bands. There is a splitting between the even integers of k and the odd integers. This can be interpreted as a very fast modulation of the bands, but it is exactly fast enough (and always will be by design, regardless of N or L) that aliasing is in play. It is very easy to connect our dots naturally into two distinct bands rather than a highly oscillatory single band.

It's a curious construction that feels similar to dimerization. But instead of cutting the Brillouin zone in half, we've maintained the same size. Instead we've doubled the spacing between k values.

If the total number of sites is even 2N, then antipodal is easy to achieve and we can split the two bands completely. If the total sites is odd 2N+1 then I think that the bands have to have dirac points? Also the dirac points are not degenerate. There is only 1 state at exactly the point.

Now an antipodal tunneling seems ridiculous. I've only got a couple defenses. 1 Just an theoretical interesting exercise that maybe can avoid some no go theorems that assume locality 2. count on some hail Mary quantum hocus pocus topological order to make the mean field hamiltonian  3. the mobius strip interpretation.

A mobius strip needs to be traversed twice in order to get back to where you were. Also, halfway around, you're on the opposite side of the paper as you started, so in some sense you are very close to the beginning. This model has that feel. If you had a chain of atoms in a mobius strip configuration (a single chain that loops over itself twice) with kind of weak tunneling transverse to the chain, this doesn't seem entirely crazy.

In all honesty, I've been playing around with this idea because I was trying to make a quantum model on the projective plane using the identification of antipodal points on the sphere. And the reason I was doing that was because I was trying to find a translation invariant form of dimerization (or making a pseudospin). That problems is harder though. I need to use spherical harmonics as best I can figure. But spherical harmonics don't have finite N.

You can identify points on a torus. This is a 2d generalization that you can push through.

It's not clear to me that the model has interesting topological properties or not. It is a funny fellow though. And it is sufficiently weird that one wonders if it avoids the assumptions of no-go theorems (Nelson-Ninomiya)
