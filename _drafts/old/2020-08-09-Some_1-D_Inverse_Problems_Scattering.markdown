---
author: philzook58
comments: true
date: 2020-08-09 02:57:25+00:00
layout: post
link: https://www.philipzucker.com/?p=2675
published: false
slug: Some 1-D Inverse Problems, Scattering
title: Some 1-D Inverse Problems, Scattering
wordpress_id: 2675
---




What is a good way to simulate standard scattering problems.







Waves in randomized media ~ quantum field theory







Ishimaru, Sheng, Imry, mesocscopic







[https://en.wikipedia.org/wiki/Computational_electromagnetics](https://en.wikipedia.org/wiki/Computational_electromagnetics)













02/20







Inverse problems are neat. They combine physics with sort of engineery mathematics, and it's a problem that is easy to motivate. You want to look inside a person and figure out what's goin on, or look in the ground for ore. Things like that.







1-D inverse problem. Sometimes it's tough to imagine how you could get enough info from a 1-D system at it's edges.  Phase shift. Travel time tomography







$latex E = \frac{1}{2}mv^2 + V(x)$  $latex v = \frac{dx}{dt} \sqrt{ \frac{2 (E-V)}{m} } $  $latex dt =\frac{dx\sqrt{m}}{\sqrt{2(E-V)}}$







The data we get out is $latex T(E)$, the total travel time as a function of energy. Assuming that the potential is attractive for simplicity, so that we don't have to account for bounce back. If we take a piecewise constant model of the potential V, we can do the individual chunks of the integral. $latex T(E) = \sum \frac{\delta x_i \sqrt{m}}{\sqrt{2(E-V_i)}}  $. This is obviously not uniquely solvable. It is completely symmetrical in the different potential.







The WKB approximation is a semiclassical approximation for waves. In addition to the rough travel time, we can estimate perhaps phase shift that is collected is $\int E dt$ ... uh $latex \int p dx  = \int \frac{2m(E-V)]$.  







For a 1-D resistor based circuit, you also can't get the much data out. You can only determine the effective resistance of the region. It is interesting to formulate this as an ODE problem just for comparison with later stuff. $latex \sigma \partial_x V = I$ or equivalently $latex \partial_x V = \rho I$ where $latex \rho $ is the resistivity =$latex R / dx$ and $latex \sigma $ is the conductivity. The conversation of current applied to this gives. $latex \partial_x (\sigma \partial_x V) = 0$ . We can lay out V in a sampled point vector and approximate the derivatives with finite differences. In this case it is most natural to associate conductivity variables with the edges between sample points.













Mechanical inverse problem, given the time it takes for a particle to come in and out at different energies.







Geometrical inverse problems have a binary kind of flavor. Legendre transform basically gives the solution to a convex region. A 1-D binary problem is not very interesting, but it is very easily solved. If you only know whether a probe bounces back or goes through (or if current flows steady state versus doesn't) , you can detect if there is a barrier or not. If you can time the probe, you can know the location of the outermost barrier. distance from measurement position L = t/v. Simple enough. The simpler something is, the more universally useful it is. This is used for example to know where breakages are in transmission lines. Send in a voltage  pulse and see how long it takes to come back. Or ultrasonic range detectors.







The Laplace equation describes many systems. Temperature, Voltage,  Current. We might have temperature, voltage or current measurements on the boundary of a region measuring







A simple inverse problem is to determine sources gives the voltages at the edge $latex \nabla^2 \phi = j$  $latex (\nabla^2)^{-1} j = \phi $.







A version of this is to consider a finite number of sources at known positions. They output a coulomb potential. We can the estimate fairly straightforwardly the graviational mass at each position based on field measruements. These measurements are going to be somewhat insensitive though. The coulom potential tends to smooth things out.







Alternatively, we might know there are 5 masses of known size, and we wish to estimate their position. Either we can non-linearly parametrize the positions, or we can transition into the field picture and use a MIP.







Estimating both position and size of the charge becomes the linear problem again.







A more motivated inverse problem is to determine the constitutive parameters as a function of the edge. It is less clear how to solve this. One simple way, the analog of the born approximation, is to use perturbation theory.







The x-ray extinction problem is to consider an x-ray traveling through a material with an extinction per distance $dA = - \alpha dx $. We can see the total extinction on a line traveling through the patient. $latex e^{-\int \alpha(x)dx}. The goal is to from many such sampled integrals, estimate $latex \alpha(x)$.







Compute vision is another kind of geometrical inverse problem. Given rays coming into a pupil, determine where they came from and how they were produced. This is very interesting from some conceptual perspective. We're interested in relativity, what would this weird phenomome look like? There is a penrose rotation where a moving object appears to rotate as it goes by you. Gravitational Lensing. In gravity, notions of time and space we're used to coinciding no longer do. They are merely in relation to one another.







Scattering problems are a kind of inverse problem.







Paraxial Optics and The Schrodinger Equation - Marcuse



