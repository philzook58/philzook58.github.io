---
author: philzook58
comments: true
date: 2018-12-23 03:10:13+00:00
layout: post
link: https://www.philipzucker.com/a-simple-interior-point-linear-programming-solver-in-python/
slug: a-simple-interior-point-linear-programming-solver-in-python
title: A Simple Interior Point Linear Programming Solver in Python
wordpress_id: 1541
categories:
- Optimization
tags:
- optimization
- python
---

This solver is probably not useful for anything. For almost all purposes, let me point you to cvxpy.

If you want an open source solver CBC/CLP and GLPK and OSQP are good.

If you want proprietary, you can get a variable number constrained trial license to Gurobi for free.

Having said that, here we go.



The simplex method gets more press, and certainly has it's advantages, but the interior point method makes much more sense to me. What follows is the basic implementation described in Stephen Boyd's course and book [http://web.stanford.edu/~boyd/cvxbook/](http://web.stanford.edu/~boyd/cvxbook/)

In the basic interior point method, you can achieve your inequality constraints $ \phi(x) \ge 0$ by using a logarithmic potential to punish getting close to them $ -\gamma \ln (\phi(x))$ where $ \gamma$ is a parameter we'll talk about in a bit. From my perspective, the logarithm is a somewhat arbitrary choice. I believe some properties of the logarithmic potential is necessary for some convergence guarantees.

The basic unconstrained newton step takes a locally quadratic approximation to the function you're trying to optimize and finds the minimum of that. This basically comes down to taking a step that is the inverse hessian applied to the gradient.

$ \min_{dx} f(x_0+dx) \approx f(x_0) + \nabla f(x_0)dx + \frac{1}{2} dx^T H dx$

$ (H)_{ij} = \partial_{ij}f(x_0)$

$ \nabla f(x_0) +H dx = 0 \rightarrow dx =- H^{-1}\nabla f$

We can maintain a linear constraint on the variable x during this newton step. Instead of setting the gradient to zero, we set it so that it is perpendicular to the constraint plane using the Lagrange multiplier procedure.

$ \nabla f(x_0) +H dx = -A^T \lambda \rightarrow Hdx + A^T \lambda = - \nabla f$

$ A(x_0 + dx) = b$

This is a block linear system

$ \begin{bmatrix}

H & A^T \\

A & 0 \\

\end{bmatrix}

\begin{bmatrix}

dx \\ \lambda

\end{bmatrix}

= \begin{bmatrix}

-\nabla f \\ b - Ax_0

\end{bmatrix}

$

Despite the logarithm potential, there is no guarantee that the newton step would not take us outside the allowed region. This is why we need a line search on top of the newton step. We scale the newton dx to $ \alpha dx$. Because the function we're optimizing is convex and the region we're in is convex, there is some step length in that newton direction that will work. So if we keep decreasing the overall step size, we'll eventually find something acceptable.

As part of the interior point method, once it has converged we decrease the parameter $ \gamma$ applied to the logarithm potential. This will allow the inequality constraints to satisfied tighter and tighter with smaller gamma.

The standard form of an LP is

$ \min c^T x $

$ A x = b$

$ x \ge 0$

This doesn't feel like the form you'd want. One way you can construct this is by adding slack variables and splitting regular variables into a positive and negative piece

$ x = x_+ - x_- $

$ Ax \ge b \rightarrow Ax +s = b, s \ge 0$



The interior point formulation of this is

$ \min c^T x- \gamma \sum_i \ln(x_i)$

$ Ax = b$

The Hessian and gradient are quite simple here

$ \nabla f = -\frac{\gamma}{x_i}$

$ (H)_{ij} = \delta_{ij} \frac{\gamma}{x_i^2}$

The optimum conditions for this are

$ \nabla (c^T x - \gamma \ln(x))= c - \gamma \frac{1}{x} = 0$

$ Ax=b$



Now in the above, I'm not sure I got all the signs right, but I did implement it in python. The result seems to be correct and does work. I haven't tested extensively, YMMV. It's a useful starting point.

    
    #simple lp
    
    import numpy as np
    import scipy.sparse as sparse
    import scipy.sparse.linalg as linalg
    # min cx
    # x >= 0
    # Ax = b
    
    
    
    
    
    def newtonDec(df, dx):
    	return np.dot(df,dx)
    
    # assumes that x + alpha*dx can be made positive
    def linesearch(x, dx):
       alpha = 1.
       while not np.all( x + alpha*dx > 0):
       		alpha *= 0.1
       return alpha
    
    # min cx
    
    def solve_lp2(A, b, c, gamma, xstart=None):
    	#x = np.ones(A.shape[1])
    	#lam = np.zeros(b.shape)
    	xsize = A.shape[1]
    	if xstart is not None:
    		x = xstart
    	else:
    		#xlam = np.ones(xsize + b.size)
    		x = np.ones(xsize) # xlam[:xsize]
    		#lam = xlam[xsize:]
    	while True :
    		print("Iterate")
    		H = sparse.bmat( [[ sparse.diags(gamma / x**2)   ,   A.T ],
    		                  [ A  ,                         0 ]]  )
    
    		dfdx = c - gamma / x #+  A.T@lam 
    		dfdlam = A@x - b
    		df = np.concatenate((dfdx, dfdlam))#np.zeros(b.size))) # dfdlam))
    		#np.concatenate( , A@x - b)
    		dxlam = linalg.spsolve(H,df)
    		dx = - dxlam[:xsize]
    		lam = dxlam[xsize:]
    
    		alpha = linesearch(x,dx)
    		x += alpha * dx
    		#lam += dlam
    		if newtonDec(dfdx,dx) >= -1e-10:
    			print("stop")
    			break
    
    	return x, lam
    
    
    def solve_lp(A,b,c, xstart=None):
    	gamma = 1.0
    	xsize = A.shape[1]
    	x = np.ones(xsize)
    	for i in range(8):
    		x, lam = solve_lp2(A, b, c, gamma, xstart=x)
    		gamma *= 0.1
    	return x, lam
    
    
    N = 12
    A = np.ones(N).reshape(1,-1)
    b = np.ones(1)*2
    c = np.zeros(N)
    c[0] = -1
    
    
    #print(solve_lp(A,b,c, 0.000001))
    print(solve_lp(A,b,c))
    
    
    
    
    def BB(A, b, c, best, xhint = None):
    	picked = np.zeros(xsize)
    	picked[pickvar] = 1
    	Anew = sparse.hstack((A, picked))
    	bnew = np.concatenate((b,choice))
    	x, lam = 
    	np.dot(c,x)
    	if lp_solve(Anew, bnew, c) < best:
    		best, x = BB(Anew, bnew , c, best, xhint)
    	return best, x
    
    
    
    
    '''
    #min  cx + gamma * ln(x)
    # s.t. Ax = b
    
    # cx + gamma * ln(x) + lambda (Ax - b)
    
    #gradient 
    delx = c + gamma * 1/x + lambda A
    dellam = Ax - b
    # hess
    dlx = A
    dxl = A.T
    dxx = - gamma (1/x**2)
    
    
    H @ (x l) = (delx dell)
    '''
    






Musings:

I wanted to build this because I've been getting really into mixed integer programming and have been wondering how much getting deep in the guts of the solver might help. Given my domain knowledge of the problems at hand, I have probably quite good heuristics. In addition, I've been curious about a paper that has pointed out an interesting relatively unexploited territory, combining machine learning with mixed integer programming [https://arxiv.org/pdf/1811.06128](https://arxiv.org/pdf/1811.06128)

For these purposes, I want a really simple optimization solver.

But this is silly. I should use CLP or OSQP as a black box if I really want to worry about the mixed integer aspect.

MIOSQP is interesting.

It is interesting how the different domains of discrete optimization and search seem to have relatively similar sets of methods. Maybe I'm crazy. Maybe at the loose level I'm gonna talk almost anything is like almost anything else.

Clause learning and Cutting plane addition feel rather similar.

Relaxation to LP and unit propagation are somewhat similar. Or is unit propagation like elimination?

Mixed integer programs build their own heuristics.

Fourier Motzkin and resolution are similar methods. In Fourier motzkin, you eliminate variables in linear inequalities by using algebra to bring that variable by itself on one side of the inequality and then matching up all the <= to all the uses of >= of that variable. There are packages that compute these things. See CDD or Polyhedra.jl

Resolution takes boolean formula. You can eliminate a variable q from a CNF formula by taking all the negated instances $ \not q$ and combining them with all positive instances.
