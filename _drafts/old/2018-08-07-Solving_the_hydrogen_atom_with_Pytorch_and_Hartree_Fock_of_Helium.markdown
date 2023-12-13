---
author: philzook58
comments: true
date: 2018-08-07 15:10:15+00:00
layout: post
link: https://www.philipzucker.com/?p=1191
published: false
slug: Solving the hydrogen atom with Pytorch and Hartree Fock of Helium
title: Solving the hydrogen atom with Pytorch and Hartree Fock of Helium
wordpress_id: 1191
---

The extension to 3 dimensions from the simple harmonic oscillator is not that difficult.



To get better results, we're going to need to increase the sampling with time, and lower the learning rate. The momentum helps us effectively increase the sampling.

It may be convenient to maintain an estimate of the total integral. (Actor critic anyone?)

We should switch over to a metropolis Monte Carlo integration scheme. A lot of our samples are a huge waste. Then we can think of our wavefunction as part of our policy network (determining the probabilities of the next step). The analogy isn't quite so clean because the wavefunction also is directly a part of the reward function also.

The Hartree Fock method uses a slater determinant wavefunction. Using our stochastic integration scheme, this is also a pretty easy change. Now we just need to add a det layer at the end of our model and boost up the number of input variables. Nice.
