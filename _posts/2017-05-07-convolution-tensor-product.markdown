---
author: philzook58
comments: true
date: 2017-05-07 00:14:27+00:00
layout: post
link: https://www.philipzucker.com/convolution-tensor-product/
slug: convolution-tensor-product
title: Convolution and Tensor Product
wordpress_id: 706
---

I realized a relation the other day that made me feel like a doof.

The tensored $ H\otimes I +I\otimes H $ extension of a 1-particle operator H occurs often. This is also the form of a laplacian of many variables

One of the most fantastic properties of the exponential and tensor product is

$ e^{H\otimes I +I\otimes H}=e^{H}\otimes e^{H}$

I guess that looks okay but it is worth remarking that kron multiplication meshes well with exponential.

While this is easy, the inverse is not. You can't write the inverse simply in terms of the inverses of H, as you can write the exponential in terms of the krons of $ e^H$.

At the same time, This operator is roughly the propagator $ e^{tH}$, which often you use the Laplace transformed version of $ G(E)=\frac{1}{H-E}$. But that right there gives you an interesting integral expression for the inverse of the tensor extension of H.

$ e^{t H\otimes I}e^{t I\otimes H}$ is a product in the time domain. Hence it becomes convolution in the Fourier domain.

$ G(E) =\frac{1}{H-E} (*) \frac{1}{H-E}=\int dE' \frac{1}{H-E'}\otimes\frac{1}{H-(E-E')}$

Where that star is some kind of kroneckerized convolution. It makes sense that kronecker product in the time domain becomes a kronecker convolution in the Fourier domain. If you do the integral out in an eigenvalue expansion you can see that it does work.

This suggests a kind of interesting method for finding the tensorized sum (I'm having a hard time knowing what to call it, but sums of the form $ A\otimes I+I\otimes B$ ) in terms of their original using a numerical integration.
