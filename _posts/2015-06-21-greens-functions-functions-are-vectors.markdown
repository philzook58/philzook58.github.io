---
author: philzook58
comments: true
date: 2015-06-21 23:09:38+00:00
layout: post
link: https://www.philipzucker.com/greens-functions-functions-are-vectors/
slug: greens-functions-functions-are-vectors
title: 'Green''s Functions: Functions Are Vectors'
wordpress_id: 25
---

Matrices are the only math problem man actually knows how to solve.

Everything else is just sort of bullshitting our way through the best we can.

Multiplying matrices like $ AB$ is a notation that let's us reason about very large complicated objects at a very simple level.
The convention of multiplication of matrices seems kind of arbitrary (rows times columns) but it is simple.

The two main powerful questions about a matrix we can get an answer to are what is a matrices inverse and what are it's eigenvalues.

Hence the emphasis on linear differential equations. Any problem phrased in these terms is just a matrix problem.

Here's the biggest most important point of Green's Functions. If the differential operator $ L$ is considered to be a matrix, then the Green's function $ G$ is it's matrix inverse $ L^{-1}$.

Boom.

<!-- more -->



Okay so I haven't discussed at all what Green's functions even are yet. We'll get there. To avoid the physical and concrete discussion to go into the abstract feeling one is entirely against my typical policy. But I think this is really important and beautiful. Green's functions are used in approximation schemes that have exact and obvious brothers when expressed as matrix equations. The matrix notation removes a large variety of clutter of x,y,z,t variables and integrals that obscures what you're really trying to say. It's good.

A function is a vector. Consider a function f defined in a box $ 0


At the same time, we can define very sensible matrices that will take any function and bring it to it's finite difference, or to it's finite difference approximation of the Laplacian. (Matrices are linear operations that take vectors to vectors. Derivatives and finite differences are both linear operations. The also take a function and give a function. Hence matrices are a reasonable representation.)

Now here an important subtlety arises. Boundary conditions.
Can I really map a derivative as a new function on the vertices?
Try it out for a 1-d case. Let's suppose I have a function that I sampled at $ x= 0, .5, 1$
$ \begin{bmatrix} 4 \\ 8 \\ 3 \end{bmatrix}$
What is a reasonable choice of the derivative. I claim that really there are only two values.
$ \frac{1}{.5}\begin{bmatrix} 4 \\ -11 \end{bmatrix}$
Looking at where I'd want to place them, they seem like they should be defined on the red edges connecting the blue vertices I've chosen, of which there are only two.


My derivative matrix is not square! This kind of sucks for some purposes. How am I going to take a second derivative? Gotta build a whole other matrix. Sucks.

The actual form of the matrix $ L$ will totally depend on the boundary conditions. This can confusingly be tacit in the ordinary notation like $ L=\nabla ^2$. Are we in a metal box? Sphere? Near a needle? That sort of data totally changes the nodes we pick for discretization and how we form L for the nodes on the boundary even if the matrix elements for the nodes in the interior of the domain basically always look like $ \nabla^2$. 
The Green's function since it comes directly from L also depends on the boundary conditions. $ G$ is not always $ \frac{1}{r}$! That's only true for the infinite space Laplacian Green's function. This was a big point of confusion for me at some point, which is why I'm emphasizing it now.

Well, that was kind of a blather. Eh, no one will read this anyhow.

I saw a dog once.

It was ok.







