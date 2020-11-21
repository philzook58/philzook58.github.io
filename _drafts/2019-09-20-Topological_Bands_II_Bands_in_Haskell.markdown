---
author: philzook58
comments: true
date: 2019-09-20 15:01:05+00:00
layout: post
link: https://www.philipzucker.com/?p=678
published: false
slug: Topological Bands II. Bands in Haskell
title: Topological Bands II. Bands in Haskell
wordpress_id: 678
---




The below never got published.







Brillouin has a love song to band theory







Band theory is a factoring of a periodic system into it's periodic part and unit cell.







What is topological about topological insulators. The trouble is, when we visualize bands, we almost always go for the energy diagram. But then energy diagram is not what we need. What we need it actually not particularly visualizable, except by analogy.







$latex T_n$ is the circulant shift matrix. which shifts the rows of vector by n spots when applied.







A periodic matrix (Hamiltonian) 







$latex H = \sum_n T_n \otimes U_n$







We know the basis that diagonalizes circulant matrices. It is the Discrete fourier transform basis.







$latex U_mn = \frac{1}{\sqrt{N}}e^{i 2 \pi m n / N }$







$latex U' = U\otimes I$ with transform H into







$latex U^{\dagger} H U = H' = \sum_n e^{i 2\ pi n / N} \otimes U_n $







In the limit that N grows very large we make the substitution $latex k = \frac{2\pi n}{N}$. 













We can imagine a 3-d vector getting wrapped up on a sphere.







The other thing that is topological about these things occurs in real space.  Edges modes exist in a robust way irrespective of the exact geometry.







Su-Schrieffer-Hieger model. The simplest model of edge modes and which gets at a lot of the thrust of the whole thing.







Haldane model







topological insulator models.







Edge mode models













## 2017/03/08






### Discretizing Schrodinger




To discuss band theory at the level that has some computational and conceptual teeth, we need to get to the tight binding model way of looking at things. We need to get from the continuous differential world of Schrodinger




$latex \frac{-\hbar^2}{2m}\partial_x^2 \psi + V\psi =E\psi$




to the discretized world of finite matrices.




There are a number of roads going back and forth between these worlds.




Most of the sensible discretizations one will try will preserve the Hamiltonian in the low energy sector and modify it for higher energies.




The simplest way to finitize the differntial equation is the finite difference method.




The definition of the derivative $latex \partial_x f = \lim_{a\rightarrow 0} \frac{f(x+a/2)-f(x-a/2)}{a}$




The simplest thing to make this numerically computable is to remove to limit taking a to 0 and make it a small but finite size. This is replacing tangent lines to the graph of f with secant lines. When the feature sizes (lumps and changes) of f is larger than a, this should work well. The second derivative becomes a second application of this formula




$latex \partial_x^2 f \approx \frac{f(x+a)-2f(x)+f(x-a)}{a^2}$




If we pack our samples of the function f into a vector v such that $latex v_n = f(na)$ we can write the second derivative as a matrix operation, since the second derivative is a linear combination of the samples of f. This is THE paradigm for thinking about differential equations.




**The linear operator contains BOTH the differential equation AND the boundary conditions. ALWAYS.**




The finite matrix form makes this clear. Different boundary conditions will change entries in the matrix.




$latex \nabla^2 G(x,x')=\delta(x-x')$




$latex \nabla^2\phi = \nabla^2 \int dx'G(x,x')\rho(x')=\int dx'\delta(x-x')\rho(x')=\rho(x)$




The green's function corresponding to a linear operator is just the inverse of the matrix of that linear operator. It will depend on boundary conditions, because boundary conditions are always part of the operator.




$latex KG=I$




$latex \delta(x-x') = (I)_{xx'}$




 




Another approach is the linear combination of atomic orbitals approach. The idea is for atoms in isolation, the ordinary atomic orbitals would be the lowest energy eigenfunctions of the Hamiltonian. Howver, now that the aotms are close, these orbitals overlap and electrons can skip and tunnel between them, so they are no long eigenfunctions.




 




Any single particle picture is a lie. Why does the single particle Schrodinger equation apply? Where does the periodic potential that we'd use the Bloch theorem on come from? Why are the linear combination of atomic orbitals the right thing to do? We are not starting from first principles really. Let's at least tell convenient lies.
