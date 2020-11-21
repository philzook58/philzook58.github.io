---
author: philzook58
comments: true
date: 2018-01-11 03:42:09+00:00
layout: post
link: https://www.philipzucker.com/?p=908
published: false
slug: 'Rosetta Stone: Reinforcement Learning and Quantum Physics'
title: 'Rosetta Stone: Reinforcement Learning and Quantum Physics'
wordpress_id: 908
---

Reinforcement Learning (and optimal control) are areas where analogies with quantum mechanics are plentiful and illuminating if you have more experience with one field than the other



wavefunction <-> probability distro

N-Body QM <-> n-parameter state. In Slam for example, may track very large number of correlated features

Linear dynamics (SHO, free particle). Physics is all in all way more reliant on the linear paradigm. <-> Linear dynamics

QFT <-> Controllable fields? Like sound or velocity flow. Images are field like. Perhaps some kind of lattice-like or elastic robot. Fields are atypical in control type applications. Numerical nightmare. Perhaps with methodology and computational power someday they won't be. You could integrate an entire FEM solver into your control algorithm.

mean field <-> average behavior

RPA <-> fastslam

Path integral <-> time series probability distro

annihilation and creation op <-> ?

Fermion, Boson <-> Probably N/A. All particles are discernable

Phase <-> Probably N/A

perturbation theory <-> Probably rarely used explicitly . More Numerical. Iterative linearization is implicit perturbation theory.

Hubbard Stratonovich <-> Secret State?

topological problems - particle on circle <-> weird  robotic topologies.

TQFT, Edge modes, Anyons, topological dislocations <-> ? Probably have to work hard to conceive of classical analogs.

Gauge fields <-> ?

tensor networks? <-> Deep learning? Lot's of buzz in this area largely driven by the buzz around deep learning. If you squint, diagrams of convolutional neural nets and renormalizing tensor networks look very similar.

renormalization <-> ? Maybe training simplified models on the more complex ones?

regularization <-> regularization. The typical forms they take is very different (momentum space cutoff, lattice spacing, pauli-villars, dimensional) vs (tikhonoff, dropout). Tikhonoff and Pauli-Villars are the closest. Lattice spacing and Momentum cutoff are both forms of just keeping the model low dimensional enough. The two concepts don't quite coincide in terms of their philosophy.

?  optimal quantum control is a field <-> optimal control

Hamilton-Jacobi <-> V and Q functions

Lagrangian <-> cost function that is integrated

? Perhaps source terms or forcing terms J. Usually used as generating functions no to optimize over. No that's not true. Optimized over in deriving effective lagrangians. Find best classical J to simulate complicated interaction and substitute in. <-> control function

time <-> time

?  <-> Model Free

Measurement <-> Not measurement. The two notions are very different. quantum measurement and control is largely  about how measurement destroys the quantum nature of the state, non commutativity of variables, and other quantum weirdness. Measurement in a classical system is a separate topic that deals with other issues. At a high cursory level, they may sound similar. Beware.





Metropololis Algorithm uses markov chain to sample difficult integrals.

By analogy to RL, the policy in this case is the boltzmann factor or wavefunctionsqaured

The thing to minimize is a variational principle. Hence, one could apply RL agorithms to perform Monte Carlo Variational estimates.

V function is estimate of energy conditioned upon current metropolis confguration (we could be in a bad spot or good spot.).  Q function is... peculiar? Advantage function may tell us how uncharactersitc our current conifg is

The reward directly depends on the policy itself. That is peculiar. Can that be modelled as depednece on action? Do need to rework derivation for policy gradient

I guess this is unlikely to work well. Reward estimates are not accurate. And policies aren't perfect. They work at best.



Ideas for wavefunction networks

shared individual wavefunctions

Det layer for fermions. it is differentiable A^-1/detA.

Antisymmettric nonlinearities maintain antisymmettry after det layer




