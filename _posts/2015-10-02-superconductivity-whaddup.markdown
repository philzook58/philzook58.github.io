---
author: philzook58
comments: true
date: 2015-10-02 14:43:32+00:00
layout: post
link: https://www.philipzucker.com/superconductivity-whaddup/
slug: superconductivity-whaddup
title: Superconductivity, whaddup
wordpress_id: 181
---

Let's try to give an explanation of superconductivity a go.

First off, there are at least two prongs, the microscopic and the macroscopic. This is ubiquitous under many topics. Hypothetically the two are linked, but in practice you don't need one for the other. For example, the microscopics of magnets coming from the electron spins and why the spins like to align vs the forces felt by refrigerator magnets. Or why electrons respond to electric field in metals vs. circuits.

On the macroscopic level you have the London equations. They are essentially just telling what the response of the material is, kind of like ohm's law for superconductors. You can derive the Meissner effect, the expulsion of magnetic field from inside the superconductor, from these guys.

On the microscopic level, you have BCS theory. The electrons are attracting each other, and they form bound states a little like a hydrogen atom called Cooper pairs.

In between the two, on what you might call the mesoscopic level, is Landau Ginzburg theory and Bogoliubov de Gennes. These more or less describe that the electron fluid is more or less moving as if the superconductor.

I think I'll start with the microscopics.

For bosons, the condensation is conceptually more straightforward. Bosons need to be in wavefunctions that are fully symmettric between the particles. If you flip any of the coordinates between particles, the wavefunction stays the same. $ \psi=x_1 x_2$ for example or $ \psi=e^{i k x_1 + i q x_2}+e^{i q x_1 + i k x_2}$.  It is possible for all the bosons to just be in the same wavefunction $ \Psi=\psi(x_1)\psi(x_2)\psi(x_3)...$. Cool. Alright. This is a good variational wavefunction to try (the variational parameters being the entire single particle function $ \psi$. Quite a lot of wiggle room! But also very constraining. Many particle physics Hilbert spaces are huge.). Maybe the bosons will like it, maybe they won't. In what situations do they like this thing? Basically, attractive potentials. In He-4 this comes from van der Waal forces (dipole dipole forces).

One of the characteristics of bosons is that they clump. They have a statistical likelihood to be near one another . The wavefunction we've picked feels extremely bosony, and it is. It exacerbates this clumping. So attractive potentials between particles will energetically prefer this wavefunction.
