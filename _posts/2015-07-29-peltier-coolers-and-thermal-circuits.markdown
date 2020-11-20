---
author: philzook58
comments: true
date: 2015-07-29 12:49:29+00:00
layout: post
link: https://www.philipzucker.com/peltier-coolers-and-thermal-circuits/
slug: peltier-coolers-and-thermal-circuits
title: Peltier Coolers and Thermal Circuits
wordpress_id: 83
---

A great many things in the world follow the paradigm of electric circuits. Electric circuits are god.

The abstraction of many things as one thing is the realm of mathematics. The mathematical reason so many things act like electrical circuits is that they are operating under physical laws that take the form of Laplace's equation $latex \nabla\cdot\epsilon\nabla\phi$.



	
  1. A Potential. The potential is connected to a more physical quantity by the gradient $latex -\nabla \phi = \vec{E}$.

	
  2. A Constitutive relation. The first vector is connected to a current by a linear relation using some material properties, ie Ohm's law or $latex D=\epsilon E$

	
  3. A Conservation Law. The divergence of the current is conserved.$latex \nabla\cdot \vec{J}=0$. What flows in must flow out. Or the divergence matches sources $latex \nabla\cdot \vec{J}=Source$.


The circuit formulation is

	
  1. $latex E=\nabla V$

	
  2. $latex \sigma E=J $ Ohm's Law in its continuous form

	
  3. $latex \nabla \cdot J =0$ Conservation of electric current


The regions with different $latex \sigma$ can be chopped up into an effective discrete circuit element problem.

By analogy we can solve other problems that take the same form, for example heat conduction.

	
  1. $latex F=\nabla T$ We don't usually call F anything, but it is the local temperature gradient

	
  2. $latex C F=Q $ Fourier's Law.

	
  3. $latex \nabla \cdot Q=0$ Conservation of heat current, aka energy conservation


From this follows the theory of thermal circuits.

Ok. So we've been trying to build a cloud chamber. We've been buying peltier coolers, which cool one side and heat the other side when you power them.



The details of using Peltier coolers has been sparse. Clearly I just don't know where to look.

Best thing I've found [http://www.housedillon.com/?tag=peltier](http://www.housedillon.com/?tag=peltier).




