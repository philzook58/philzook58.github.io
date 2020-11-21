---
author: philzook58
comments: true
date: 2017-02-20 19:20:15+00:00
layout: post
link: https://www.philipzucker.com/topological-bands-i/
slug: topological-bands-i
title: Topological Bands I.
wordpress_id: 655
---

#### Intro


Topology is the study of geometry minus the wiggles. More specifically topology studies continuous maps.

Topology separates into a number of sub fields.



 	
  * General Topology - Studies the set theoretic properties and definitions of topology

 	
  * Algebraic Topology - Studies


The piece of topology that is most relevant to physics (partially because it is the most computational) is the notion of the notion of the topological invariant. Topological invariants are numbers that can be computed. If they disagree for two objects, then the two objects are not topologically equivalent. The reverse is not true.

An example of a topological invariant is the winding number of a closed curve around a point in 2d. This can also be interpreted as a classification of mappings from circles to circles.

Another example is the Euler number. The Euler number kind of counts the number of holes in a surface. It is defined as $ \chi = V-E+F $, the number of vertices minus edges plus the number of faces in a tessellation of a surface. If one considers the Euler number of possibly disconnected surfaces or edges or vertices, the Euler number does a decent job of counting the number of objects.

Nick Read has published a [review article](http://boulderschool.yale.edu/sites/default/files/files/pt_article_published.pdf) in Physics Today. Physics Todays is a pretty excellent introduction to modern topics if you can find an article on that topic.

Topological Matter has one or more of the following



 	
  1. An energy gap above the ground state

 	
  2. A number of degenerate ground states that depends on the topology of the surface on which they live (Torus vs Sphere).

 	
  3. Anyonic Quasiparticles.

 	
  4. Quantized Response functions (quantized Hall conductance for example)

 	
  5. Unavoidable Edge Modes




#### Connections


Two objects that are far apart need to be brought together in order to be compared. A [Connection](https://en.wikipedia.org/wiki/Connection_(mathematics)) is a specification on how to transport something around in space. This connection is defined differentially. Given a tiny displacement $ dx$, what is the tiny change $dO$ in the corresponding object.

There are three examples of connections of different flavor.

The first is the connection defining parallel transport of vectors in a curved geometry.

The game goes like so: Suppose you want to transport a little arrow in the surface of a sphere  to a new point on a sphere. You want a procedure to keep the arrow in the surface of the sphere. The simplest procedure is to project the arrow back into the sphere after moving it a tiny bit $ dx$. Move, project. Move, project. This procedure keeps the arrow in the surface of the sphere the whole way. This procedure is the connection for parallel transporting the arrow on the sphere. (This procedure defines what it means for two arrows to be parallel at nearby points).

When one actually does this however, a curious thing results. The arrow upon returning to the original point after a closed loop, may have been rotated relative to the original arrow. Different paths of transport result in different amounts of turning. This turning is a result of the curvature of the sphere and the parallel transport procedure is a method by which to probe the curvature.

Rather that integrating the connection along the entire closed route, there is an alternative but equivalent way of doing the accounting. Consider a tiny loop or area $ dA$. This loop causes a correspondingly tiny rotation $ d\theta $. Because the rotation gets cancelled from traverse the same path in opposite directions, the sum of all the tiny loop rotations in an area will equal the rotation calculated for the bounding edge of that area. This is [Stokes theorem](https://en.wikipedia.org/wiki/Stokes'_theorem) about the curl if that helps.

Another connection is that of the electromagnetic [vector potential](https://en.wikipedia.org/wiki/Magnetic_potential#Magnetic_vector_potential) $ A$. The vector potential specifies how to transport quantum amplitudes and compare them at different positions. This is the [Aharonov-Bohm effect](https://en.wikipedia.org/wiki/Aharonov%E2%80%93Bohm_effect). When a particle travels through the vector potential it gets an extra phase $ \Delta \phi = q/\hbar \int A\cdot dx$.

A final connection is that connected to [Berry Phase](https://en.wikipedia.org/wiki/Berry_connection_and_curvature). Instead of talking about transport in physical geometrical space, Berry phase refers to transport in parameter space. This is analogous to the transition from cartesian coordinates in Newtonian mechanics to that of generalized coordinates in Lagrangian mechanics, which may not have a simple geometrical interpretation necessarily.

Berry phase can be interpreted as being similar to the extra phase that an oscillator might receive upon a cyclic change in its parameters for example slowly changing the length and mass of a pendulum. This seems like a small effect and it typically is a drop in the bucket compared to all the ordinary dynamic phase accumulated $ \int \omega(t)dt$ but it nevertheless exists and actually has a lot of conceptual importance.

A particularly important example of Berry phase is that of the spin-1/2. This occurs when you rotate the magnetic field that the spin is in for example.

$ u=\begin{array}{c}\cos (\theta/2)\\ \sin (\theta/2) e^{i \phi}\end{array}$

$ A=i<u\|\partial\|u>=(0, - sin^2(\theta/2) )$

$ \int A_\phi d\phi = -2\pi sin^2(\theta/2) =-\Omega/2$

$\Omega=\int \sin(\theta) d\theta \phi $ plus use some half angle identities.

In summary, the Berry phase is half of the solid angle $ \Omega$ enclosed by the path.



Next Time: Discretizing the Schrodinger Equation






