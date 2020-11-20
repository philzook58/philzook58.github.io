---
author: philzook58
comments: true
date: 2019-12-22 19:07:55+00:00
layout: post
link: https://www.philipzucker.com/solving-the-laplace-equations-with-linear-relations/
slug: solving-the-laplace-equations-with-linear-relations
title: Solving the Laplace Equations with Linear Relations
wordpress_id: 2518
categories:
- Haskell
- Physics
tags:
- categorytheory
- haskell
- physics
---




The [Laplace equation](https://en.wikipedia.org/wiki/Laplace%27s_equation) is ubiquitous in physics and engineering.







$latex \nabla^2 \phi = 0 = \partial_x^2 \phi + \partial_y^2 \phi = 0







It and slight variants of it describes electrostatics, magnetostatics, steady state heat flow, elastic flex, pressure, velocity potentials.







There are a couple reasons for that.







  * It results from minimizing the squared gradient of a field $latex |\nabla \phi |^2$ which can make sense from an energy minimization perspective.
  * Similarly it results from the combination of a flow conservation law and a linear constitutive relation connecting flow and field (such as Ohm's law, Fick's law, or Hooke's law).
  * It also gets used even if not particularly appropriate because we know how to mathematically deal with it, for example in image processing.






There are a couple of questions we may want to ask about a Laplace equation system







  * Given the field on the boundary, determine the field in the interior (Dirchlet problem)
  * Given the normal derivative of the field on the boundary determine the field in the interior (Neumann problem)
  * Given sources in the interior and 0 boundary condition, determine the field. The Laplace equation is called the [Poisson equation](https://en.wikipedia.org/wiki/Poisson%27s_equation) when you allow a source term on the right hand side. $latex \nabla^2 \phi = \rho$.
  * Given the field at the boundary, determine the derivative at the boundary. Dirichlet-to-Neumann map or [Poincare-Steklov](https://en.wikipedia.org/wiki/Poincar%C3%A9%E2%80%93Steklov_operator) operator.






Given the Dirichlet to Neumann map, you do not have to consider the interior of a region to use it. The Dirichlet to Neumann map is sort of the same thing as an effective resistance or scattering matrix. It gives you a black box representation of a region based solely on the variables at its boundary.







This [linear relation algebra](http://www.philipzucker.com/linear-relation-algebra-of-circuits-with-hmatrix/) is useful for many things that I'd have considered a use case for the [Schur complement](https://en.wikipedia.org/wiki/Schur_complement). The Schur complement arises when you do Gaussian elimination on a blocked matrix. It is good that this pattern has a name, because once you know about it, you'll see it in  many places. [Domain decomposition](https://en.wikipedia.org/wiki/Domain_decomposition_methods), marginalized gaussian distributions, low-rank update, Scattering matrices.







By composing the linear relations corresponding to the Dirchlet-Neumann relations of regions, we can build the Dirichlet-Neumann relations of larger regions.







To make this more concrete, let us take the example of electrical circuits like before. A grid of resistors is a finite difference approximation to the continuous problem







$latex -\nabla \phi = E$ Electric field is gradient of potential







$latex E = \rho j$ continuum ohm's law







$latex \nabla\cdot j = 0$ current conservation







[In this post](http://www.philipzucker.com/neural-networks-with-weighty-lenses-dioptics/), I mentioned how you can make reasonable 2 dimensional diagrams out of a monoidal category, by sort of arbitrarily flipping one wire up and one wire down as in the diagram below. This defines a horizontal and vertical composition which have to do the required book-keeping (associations) to keep an arrow in canonical form. I had considered this for the management method of weights in neural networks, but it is way more natural as the actual geometrical layout of a finite difference grid of a laplace equation.







So we can reuse our categorical circuit combinators to build a finite difference Laplace equation.





![](http://philzucker2.nfshost.com/wp-content/uploads/2019/10/My-Drawing-2.sketchpad.png)Just showing how you can bend a 4-wire monoidal box into a 2-d diagram. Ignore the labels.





This can be implemented in Haskell doing the following. Neato. 





[gist https://gist.github.com/philzook58/d61531a29e74dd7434b97ce2fb8220f1]





### Bits and Bobbles







  * Not the tightest post, but I needed to get it out there. I have a short attention span.
  * Homology and defining simplices as categories. One way of describing Homology is about linear operators that are analogues of finite difference operators (or better yet, discrete differential geometry operators / exterior derivatives). To some degree, it is analyzing the required boundary conditions to fully define differential equations on weirdo topological surfaces, which correspond to geometrical loops/holes. You can figure this out by looking at subspaces and quotients of the difference operators. Here we have here a very category theory way of looking at partial differential equations.  How does it all connect?
  * Continuous circuit models - [https://en.wikipedia.org/wiki/Distributed-element_model](https://en.wikipedia.org/wiki/Distributed-element_model) Telegrapher's equation is classic example.
  * Cody mentioned that I could actually build circuits and measure categorical identities in a sense. That's kind of cool. Or I could draw conductive ink on carbon paper and actually make my string diagrams into circuits? That is also brain tickling
  * Network circuits
  * I really want to get coefficients that aren't just doubles. allowing rational functions of a frequency $latex \omega$ would allow analysis of capacitor/inductor circuits, but also tight binding model systems for fun things like topological insulators and the Haldane model [http://www.philipzucker.com/topologically-non-trivial-circuit-making-haldane-model-gyrator/](http://www.philipzucker.com/topologically-non-trivial-circuit-making-haldane-model-gyrator/) . I may need to leave Haskell. I'm not seeing quite the functionality I need. Use Sympy? [https://arxiv.org/abs/1605.02532](https://arxiv.org/abs/1605.02532) HLinear. Flint bindings for haskell? Looks unmaintained. Could also use a grobner basis package as dynamite for a mouse.
  * This is relevant for the boundary element method. Some really cool other stuff relevant here. [http://people.maths.ox.ac.uk/martinsson/2014_CBMS/](http://people.maths.ox.ac.uk/martinsson/2014_CBMS/)






Blah Blah blah: The subtlest aspect of differential equations is that of boundary conditions. It is more correct usually to consider the system of the interior differential equation and the boundary conditions as equally essential parts of the statement of the problem you are considering. 



