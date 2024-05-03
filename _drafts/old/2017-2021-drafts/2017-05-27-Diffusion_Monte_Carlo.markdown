---
author: philzook58
comments: true
date: 2017-05-27 13:58:04+00:00
layout: post
link: https://www.philipzucker.com/?p=718
published: false
slug: Diffusion Monte Carlo
title: Diffusion Monte Carlo
wordpress_id: 718
---

The projection method / power method is the core of eigenvalue and eigenvector algorithms. Repeated application of a matrix will make the largest eigenvalued vector dominate the rest. And then you can just pull it out and find the eigenvalue by seeing how much its norm changes under one application.

Then to find the next highest eigenvector, you can project off the biggest eigenvector at every step (at least for Hermitian matrices. I'd take a slight pause to think about nonsymmettric matrices which is not usually what I'm handling).

The QR algorithm actually used by numpy (ok I have not confirmed the actual implementation is using QR but I think it is.) is basically doing this in parallel for the entire matrix rather than for one eigenvector at a time.

The projection Monte Carlo replaces the summations occuring in these matrix applications with expectation values.

Alternatively, you can note that the imaginary time Schrodinger equation looks like a diffusion equation, which come from random walks. I think this makes less intuitive sense, because why the hell would you look at imaginary time anyhow (notwithstanding a textbook told you you should).

A potential term appears like a growth or decay term if the wavefunction were a probability density.

Importance Sampling. if you already have a good variational wavefunction guess, you do not have to start from scratch while projecting. One can perform a kind of canonical transformation or half-solution like you might for switching from the schrodinger picture to the interaction picture. It also kind of has the appearance of a nonunitary gauge transformation. In the diffusion pciture, this adds a drift velcocity to walkers. Looking at the evolution of $latex f(R,t)=\psi_T(R)\phi(R,t)$

The Sign Problem. I'm not sure I entirely understand the nature of the sign problem. Naively, a

Fixed Node. If you fix the nodes of the fermionic wavefunction you are kind of doing a funny variational method.


