---
author: philzook58
comments: true
date: 2020-08-19 16:44:31+00:00
layout: post
link: https://www.philipzucker.com/?p=2934
published: false
slug: Noether and Olver. Conservation Laws and Lie brackets
title: Noether and Olver. Conservation Laws and Lie brackets
wordpress_id: 2934
---




I swear I must have more notes on this somewhere.







Noether's original paper. We listened to a podcast on Noether in the car. Interesting lady. Does noether's theorem intrinsically require an action formulation?







Sympy pointers. Sigfpe.







We're considering flows. We are parameterized by time. Solutions are paths. Conserved quantities are the functions that evaluated along a path remain the same. $latex \frac{d}{dt}C= (\dot{x} \cdot \nabla + \partial_t) C= 0$. We can derive conserved quantities (sometimes) by considering a space of functions for example polynomials. Given the equations of motion, we can derive constraints on functions. The initial condition is a conserved quantity.







We can also approach via a sampling method. Simulate the system many times and plug in those values to a parametrized set of functions. Minimize the square of the derivative or something like that. Maybe all pair differences for entire paths. Boom. A reasonable approximate invariant.







Another thing we may go about doing is transforming solutions to other solutions. This will change the initial conditions too. Sometimes the transformations are continuous. This is then another flow / another system of odes that has some relation with the first. We can write down the conditions for some flow to take solutions to other solutions.







There is this notion of considering y' to be a free variable p. Some extra side conditions constrain this. We can derive differential equations from equations for  surfaces.







Revisitting some of the stuff from sigpe  
Olver  
sympy documentation  
polynomial certificate paper







Lyapunov's method - termination metrics







Loop invaraints - a differential equation is a very loopy loop  
lamport - the basic method is invariants







energy and momentum  
symmettry and noether's theorem







approximate invaraints, actiona angle coordinates and adiabatic theorem







Lie derivative - how a function changes with time according to along flow  
Basically the material derivative.







SHO







Can we derive invaraint functions?







Olver method of like extending the number of variable.  
prolongation







This is finding a coordinate transfromation







Can we use taylor models to find an approximate invaraint?







Lie groups for solving differential equations like group groups solved polynomial equations  
http://www.physics.drexel.edu/~bob/LieGroups/LG_16.pdf      https://www-users.math.umn.edu/~olver/t_/symcl.pdf







Right… the other thing is we want to have a generator of new solutions  
So we can create an infinitseimal generator that carries things around







It does seem pretty funky that we are using a function description of a surface when everything feels so algerbaic







that python module that had smith form in it







Solving Differential Equations by Symmetry Groups







[https://www.researchgate.net/publication/233653257_Solving_Differential_Equations_by_Symmetry_Groups/link/02e7e528697b277bc9000000/download](https://www.researchgate.net/publication/233653257_Solving_Differential_Equations_by_Symmetry_Groups/link/02e7e528697b277bc9000000/download)







Brings up a good point.







Consider a family of curves x^2 + y ^2 = c^2, one could imagine fucking this all up by removing the constant by differentiation  
2x + y y' = 0  
This is now a differential equation.







what the hell is prologation? Prolongation showed up in an syntehtic differential geoemtry book  
What does this Lie method have to do with hamilton-jacobi mechanics.







Approximate invaraints in thoughtbooks



