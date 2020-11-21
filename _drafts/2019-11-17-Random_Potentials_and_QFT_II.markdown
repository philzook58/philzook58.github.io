---
author: philzook58
comments: true
date: 2019-11-17 21:25:44+00:00
layout: post
link: https://www.philipzucker.com/?p=161
published: false
slug: Random Potentials and QFT II
title: Random Potentials and QFT II
wordpress_id: 161
---




Analysis of random potentials has close connections to quantum field theory. This is because the probability distribution $latex P[V]$ is a thing of the same shape as the wavefunction of a quantum field $latex \Psi[\phi]$.







There is a big difference however in that sampling probability is much easier than computing quantum stuff.







We could image for example a gaussian distributed random field $latex P(V)=e^{\int |V(x)|^2dx}$  or perhaps something with a changing standard deviation P(V)=e^{\int \frac{1}{\sigma(x)^2}|V(x)|^2dx}$. Or perhaps something who's derivative fluctuates randomly P(V)=e^{\int|\nabla V(x)|^2dx}$.







It is easy enough to calculate quantities in the presence of these potential by sampling. But we can also try to calculate them by analytic expansion and compare. This is distinction with quantum field theory where it is more difficult to calculate by sampling (maybe in the thermal case its doable).







Ok. So what does one want to know?







  1. The spectrum. Perhaps the joint distribution function of the spectrum
  2. Average time evolution






We expect to need to calculate perturbatively in the potential if we can't figure out how to do these calculations exactly. These are standard techniques taught in quantum mechanics courses.







Born Series. [https://en.wikipedia.org/wiki/Born_series](https://en.wikipedia.org/wiki/Born_series) We can convert the Schrodinger equation into an integral form.







$latex i \partial_t \psi = H_0 \psi + V \psi$







$latex \psi(t) = \psi_0 + i \int dt' G_0(t,t')V\psi(t')$







$latex G_0(t,t') = e^{i H_0 (t - t')}$







How can I do show this? Sympy? My own DSL? Obviously, I was just spit ballin. I think this is roughly the right form.







If you plug the bottom form into the top equation, you can see that it satisfies the Schrodinger equation.







We can then develop the Born series via iteration of this equality.







Now we have $latex <\psi(t)> = <V> + <VV> + $ a relation determining the expected time evolution of the wavefunction in terms of the moments of the potential.







Time independent perturbation theory is used for perturbation of the spectrum. This can also be determined in terms of the moments of the potential.







## 9/2015






So where I was going (with great confidence) was towards the analogy that this moment equation is quite similar what one would expect from two interacting particles.




The new AVERAGE hamiltonian is still that for two noninteracting particles, but the average green's function or propagator is much more similar to that for interacting particles.




We can then pull that info in to get a better estimate of the single particle green's function.




The really really 0d example




$latex \partial_t \psi =i( \omega_0 + V)\psi$
