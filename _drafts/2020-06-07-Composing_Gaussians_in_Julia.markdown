---
author: philzook58
comments: true
date: 2020-06-07 15:40:22+00:00
layout: post
link: https://www.philipzucker.com/?p=2833
published: false
slug: Composing Gaussians in Julia
title: Composing Gaussians in Julia
wordpress_id: 2833
---




The Gaussian integral is a cutie. 







In matrix format it looks like this $latex \int dx e^{x^T A x + b^T x} $. 







Performing multidimensional Gaussian integrals is done by linear algebra essentially. That is where the beef lives. Gaussian integrals are linear algebra in disguise.







Gaussian integrals are ubiquitous in science and engineering. The central limit theorem means that probability distributions tend to be Gaussians. The Boltzmann factor mean that quadratic energies result in Gaussian integrals in statistical mechanics and quadratic energies are also ubiquitous. The Gaussian occurs in the green's function of the heat equation, Schrodinger equations. Relatedly, the Feynman path integral also performs Gaussian integrals over quadratic Lagrangians.







Gaussians are closed under partial integration. If you integrate some of the variables out of a Gaussian, the result is also a Gaussian. This is an extremely remarkable property. The linear algebraic operation this performs is the [Schur complement](https://en.wikipedia.org/wiki/Schur_complement), perhaps my favorite concept in all of linear algebra. What I find so cool about it is that it gives a vocabulary for discussing effective equations resulting from projecting/solving out variables in a linear system. It is also useful in domain decomposition and other interesting techniques.













Dirac Delta functions should be considered as generalized Gaussians. Sometimes, they are described as the limit of an infinitely sharp Gaussian. This is important from a mathematical aesthetic standpoint. You want an notion of identity if you have a notion of composition. That can turn something into a Category, and indeed Gaussian integrals can be viewed in such a way that 







However, this extension does complicate what linear algebraic computation is being performed. It is no longer a Schur complement. Instead, Gaussian integrals with delta functions are performing something similar to quadratic optimization with linear constraints. 















