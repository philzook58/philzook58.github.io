---
author: philzook58
comments: true
date: 2018-12-07 22:59:52+00:00
layout: post
link: https://www.philipzucker.com/?p=1190
published: false
slug: 'Semidefinite Programming and quantum mechanics: Particle in a Box to Hartree
  Fock'
title: 'Semidefinite Programming and quantum mechanics: Particle in a Box to Hartree
  Fock'
wordpress_id: 1190
---

It turns out that requiring a matrix to be positive semidefinite (all non-negative eigenvalues) is a tractable constraint.

The essence of the implementation of semidefinite programming is that the $latex ln(det A) = \sum \ln (\lambda_i)$ is convex in the entries of A and feasibly differentiable.

You can then use this term in a barrier method.

There us a big ole course on semidefinite programing in quantum information

[https://cs.uwaterloo.ca/~watrous/CS867.Winter2017/](https://cs.uwaterloo.ca/~watrous/CS867.Winter2017/)

One intriguing use of semidefinite programming for me is to directly express a quantum mechanical problem in terms of it's density matrix.

a density matrix is a Hermitian matrix whose trace is 1 and with all positive eigenvalues. All of these constraints are expressible within the framework of semidefinite programming.

The semidefinite program for the variational ground state problem looks like

$latex min tr H\rho$

$tr \rho = 1$

$\rho^\dagger = \rho$

$\rho \ge 0$

The constraint for keeping the state normalized feels a little better to me in this form than in the wavefunction form, where it is a quadratic constraint in the wavefunction, but your opinion may differ. You may choose to remove these constraints by explicitly parametrizing $latex \rho$ to have them by definition.

Just as a toy, let's do the particle in a box.

    
    import cvxpy as cvx
    import numpy as np
    from scipy.linalg import toeplitz
    import matplotlib.pyplot as plt
    import scipy.sparse as sparse
    
    N = 50
    rho = cvx.Variable((N, N), PSD=True)#hermitian=True)#PSD=True, complex=True, hermitian=True)
    # only one at a time. Real eigenfunctions means we could just use PSD
    col = np.zeros(N)
    
    col[0] = -2
    col[1] = 1
    H = toeplitz(col)
    
    diagonals = [[-2]*N, [1]*(N-1), [1]*(N-1)]
    H = sparse.diags(diagonals, [0, -1, 1])
    H = cvx.Constant(H)
    #print(H)
    
    obj = cvx.Minimize(cvx.trace(H@rho)) #cvx.real needed for hermitian version
    constraints = [cvx.trace(rho) == 1] #, rho >> 0]
    prob = cvx.Problem(obj, constraints)
    prob.solve()  # Returns the optimal value.
    print("status:", prob.status)
    print("optimal value", prob.value)
    #print("optimal var", rho.value)
    
    
    plt.plot(np.diag(rho.value))
    psi = np.sin(np.linspace(0,np.pi,N+2))[1:-1]
    norm = np.linalg.norm(psi)
    plt.plot(psi**2 / norm**2)
    plt.show()
    
    
    






Higher energy states are easy to state also. The orthogonality constraint is $latex tr \rho_0 \rho = 0$

    
    constraints.append(cvx.trace(rho0 @ rho)==0)


Doesn't actually work that well though.

[![eig2](http://philzucker2.nfshost.com/wp-content/uploads/2018/08/eig2.png)](http://philzucker2.nfshost.com/wp-content/uploads/2018/08/eig2.png)

The orange is the actual second psi^2. Looks like I've got a strong mix of the ground state in there

For a single particle problem, there doesn't seem like much benefit, but it seems conceivable to me that a many-body problem might have a nice formulation in the density matrix form. Presumably you are parametrizing the big ole density matrix in some heuristic way, but still, interesting

The fermion and boson problem become easy to formulate in this language also.

Although we are in a sense wasting space by not abusing these permutation constraints



just put in the anti symmettry and symmettry constraints directly.

link.aps.org/pdf/10.1103/PhysRevA.13.927

Hartree Fock: alternate factors. $latex \rho = \rho \rho$ . One of the $latex \rho$ is from the previous iteration. Uh. Maybe it's not that easy. But close?

You can get the lowest N states to fill out by creating the constraint 0 <= rho <= 1/N with tr rho = 1. Or rather tr rho = N, 0 <= rho <= 1.

rho_1 = tr_a rho_2 -- single particle density matrix is trace of two particle

0 <= rho_1 <= 1

rho_2 antisymmettric

tr rho_1 = N

Well, why even have rho_1? It feels natural for some reason.

I'm confused as to why this is inexact actually. It surely must be. I didn't derive it from anywhere though. I just guessed it. No it is.. I think we need to alternate rho1 and rho2.

rho3 ~ \sum -1 rho2 rho1. A single laplace det expansion (N terms).

Use previous rho1 or use previous rho2 to linearize (or mixture of both?). We might be pushing slightly beyond Hartree Fock. Not sure.

Is this also the BdG eqs? Allowing an explicit rho2 leaves room for it to have large factor.

Time-Dependent formulation, apply 1+iHdt once approximately, fit new rho2 rho1. Can record total accumulated loss from fitting cost function too, so have some metric of how well we're doing.

CVXPY

What the hell is this:

[https://ncpol2sdpa.readthedocs.io/en/stable/index.html](https://ncpol2sdpa.readthedocs.io/en/stable/index.html)

https://peterwittek.com/sdp-in-python.html

https://irene.readthedocs.io/en/latest/index.html

SOS.

A polynomial that has a negative value cannot be written as a sum of squares

Minimizing expected value of a function with respect to some probability.

A function is linear in some function basis.

E[f]=\int p(x)f(x). Let's suppose we're on a square domain an can expand into fourier modes. We introduce a finite cutoff. Probably a delta function will work best but we can't get there. We have the fourier expansion of the function f. We need to minimize the sum $latex sum p_n f_n$ subject to p_0=1. Also to be a probability, p > 0 for all x. Why is it important that it is a probability? Well, using a negative value would be cheating in regards to optimization.  That one is tough to state in terms of it's fourier modes. If the function is the square of something it will be > 0 , then it is the square convolution of something in the fourier domain. We can relax this to \Omega^\dagger p \Omega \ge 0

https://people.orie.cornell.edu/miketodd/orie6327/lec11.pdf





We could easily do slicing of cvxpy expressions using the numpy embedding technique. In regards to the hartee-fock formulation






