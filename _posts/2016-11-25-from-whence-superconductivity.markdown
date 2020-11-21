---
author: philzook58
comments: true
date: 2016-11-25 16:47:16+00:00
layout: post
link: https://www.philipzucker.com/from-whence-superconductivity/
slug: from-whence-superconductivity
title: From Whence Superconductivity?
wordpress_id: 572
tags:
- superconductivity
---

The self-energy used to be weird to me. But now it makes sense after I found out about the Schur complement. It can make sense even to have the decaying part of the self-energy, making an effectively non-unitary evolution of your single particle wavefunction, if there is a huge space for it to leak into, or if you approximate the Schur complement.

But how do you get the effective superconducting term from Schur complements? $ a^\dagger a^\dagger $? And how do you get the ground state to be a superposition of different particle number states?

The story that made sense to me about superconductivity is that if the 2 particle density matrix factorizes well, then that factor is the pairing wavefunction. I don't know how that can fit into my current approach. Some systematic way of factoring the interaction term? That would be nice for plasmons and such, but also is alarming because it becomes clear that you're never going to get out more for the computation than you put in. Maybe that is a truism.

It seems to me that since particle are actually conserved, we need to attach the system to external leads.

So first off, if you had a lead attached with such terms, schur complementing that lead out will almost certainly induce the term into the effective hamiltonian in the interior of the system. That is the proximity effect, where a superconductor placed next to an ordinary material will infect the material with superconductivity for a small distance (this is related to the coherence length/ size of cooper pairs in the superconductor. I've never really had those straightened out precisely.)

Now perhaps, if the interacting term is attractive, we can use this lead as a way to soften the number conservation constraint. Perhaps the lead doesn't need to be superconducting.

Alternatively the "lead" could be an identical copy of our system instead. Or maybe an infinite number of copies leading to a huge homogenous sample.






