---
author: philzook58
comments: true
date: 2018-08-16 14:56:30+00:00
layout: post
link: https://www.philipzucker.com/?p=1217
published: false
slug: Chladni patterns
title: Chladni patterns
wordpress_id: 1217
---

The vibrations of a plate are going to be the eigenfunctions of the laplacian on that plate

To draw with these patterns, we want a superposition of the modes such that it leaves nodes in the locations we want sand and non-nodes everywhere else

$latex \psi(x) = \sum a_\omega \phi_\omega(x)$

One suggestion is to try to minimize the magnitude squared of the node locations while keeping the total sum squared magnitude = 1. This is the same as the variational method, so basically we want to find eigenvalues of a matrix formed from the dot product of the node structure and eigenvectors.

$latex \min (n \cdot \psi)^2 = \sum a_i a_j (\phi_i \cdot n) (\phi_j \cdot n$

Oh actually, we want the dot to occur outside the square. We don't want cancellation, we want each individual location to be 0.

$latex \min \sum_x (n_x \psi_x)^2 = \sum a_i a_j \sum_x(\phi_i_x n_x) (\phi_j_x n_x$

This is an $latex \Omega \times \Omega$ matrix. May want to promote smoothness. The could be done by adding a laplacian term, which is diagonal because of our mode decomposition.

$\sum a_i a_j ((\phi_i \cdot n) (\phi_j \cdot n) + \alpha \omega_i \omega_j)$

We would also like the antinodes to be nonzero. This is another term we could add $latex -\sum_x((1-n)\psi)^2 $

I'm concerned that this may not be sufficient. There is an analogy that the nodes are high potential regions of a quantum particle. If the regions cut off, There will be many independent modes. An alternating coloring (positive and negative magnitude) of the picture may not be possible (we need four colorings in general). Maybe we could quickly switch between two different combinations? Would going beyond the least squares paradigm be helpful? Maybe use absolute value?

Or we could use the smoothing + node form and then iteratively add terms to increase small guys that need to be big guys (polishing esque).

We may want to include response functions in our calculations and perhaps optimize plate shape. Symmetric plates are only going to be controllable symmetrically unless we have multiple located transducers



We can calibrate the driving force by superposing 2 frequencies and balancing the magnitudes
