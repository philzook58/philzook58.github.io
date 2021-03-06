---
author: philzook58
comments: true
date: 2018-05-11 16:04:01+00:00
layout: post
link: https://www.philipzucker.com/analytic-center-python-using-scipy-numpy/
slug: analytic-center-python-using-scipy-numpy
title: Analytic Center in Python using Scipy and Numpy
wordpress_id: 1066
---

The analytic center for a set of inequalities $ \phi(x)<0$ is the minimizing position of $ \sum -\ln (-\phi(x)) $. In particular it is often used with linear inequalities. It gives a reasonable and easily computable for convex constraint function center of the region. The hessian at that point can give you a reasonable ellipse that approximates the region too (both interior and exterior approximation).

I wrote a program for linear inequalities. It is not particularly robust. First I get a feasible point using the LP solver in scipy. Then I give the appropriate gradients and Hessians to a newton conjugate gradient solver in scipy. It does return a reasonable center, but I had to fiddle with some epsilons to avoid logarithms exploding and to avoid the hessian being so big it overwhelms the gradient. Possibly a couple burn in steps of gradient descent might help, or getting a feasible point that isn't optimal since the optimal points being on the boundary is a huge problem. If the newton solver comes back with only 1 or 2 iterations, it probably failed.

    
    import numpy as np
    import scipy.optimize
    
    
    # Anaytic Center Finding
    
    def analytic_center_fun(x, A, b):
    	q = np.dot(A,x)-b + 1e-8
    	val = np.sum(np.log(q)) 
    	grad = np.sum((1./q).reshape((-1,1)) * A, axis = 0)
    	hess = np.sum( (-1./(q*q)).reshape((-1,1,1))  *  A.reshape((-1,-1,1))   *    A.reshape((-1,1,-1)), axis = 0)
    	return val, grad, hess
    
    def analytic_center_hess(A, b):
    	def hess_fun(x):
    		q = b - np.dot(A,x) + 1e-8
    		hess = np.sum( (1./(q*q)).reshape((-1,1,1))  *  np.expand_dims(A, axis=2)   *   np.expand_dims(A, axis=1) , axis = 0)
    		return hess
    	return hess_fun
    
    def analytic_center_grad(A, b):
    	def grad_fun(x):
    		q = b - np.dot(A,x) + 1e-8
    		grad = np.sum((1./q).reshape((-1,1)) * A, axis = 0)
    		return grad
    	return grad_fun
    
    def analytic_center_val(A, b):
    	def val_fun(x):
    		q = b - np.dot(A,x) + 1e-8
    		val = - np.sum(np.log(q))
    		return val
    	return val_fun
    
    def get_feasible(A,b):
    	#returns a feasible point for Ax < b
    	# need to make the inequalities a little tighter so that the logarithms aren't freaking out
    	res = scipy.optimize.linprog(-np.random.random(A.shape[1]),A_ub = A, b_ub = b - 1e-5, method='interior-point')
    	if res.success == True:
    		return res.x
    	else:
    		print("failure to find feasible point ", res)
    		return "FAIL"
    
    def analytic_center(A,b):
    	print("Calulating Center")
    	x0 = get_feasible(A,b)
    	print(x0)
    	#xc = scipy.optimiatzew
    	#xc, fopt, fcalls, gcalls, hcalls, warn 
    	# Had a problem where the hessian is too big at the boundary. Let it stop there
    	# The stopping condition is based on delta x rather than grad?
    	# Could maybe do some burn in with a couple gradient steps.
    	res = scipy.optimize.fmin_ncg(f = analytic_center_val(A,b), x0 = x0, fprime = analytic_center_grad(A,b), fhess = analytic_center_hess(A,b) )
    	xc = res
    	print(res)
    	print(xc)
    	return xc
    
    # Make a convenient box where I know where the cneter will be
    A = np.array([[1.0 , 0],
    			  [-1.0, 0],
    			  [0   , 1.0],
    			  [0.  , -1.0]])
    b = np.array([20,10,1,0])
    
    #analytic_center(np.random.random((100,10)), np.random.random(100))
    print(analytic_center_val(A,b)([0.5,0.5]))
    print(analytic_center_grad(A,b)([0.5,0.5]))
    print(analytic_center_hess(A,b)([0.5,0.5]))
    
    print(analytic_center_val(A,b)([0,0]))
    print(analytic_center_grad(A,b)([0,0]))
    print(analytic_center_hess(A,b)([0,0]))
    sol = analytic_center(A,b)
    
    print(analytic_center_val(A,b)(sol))
    print(analytic_center_grad(A,b)(sol))
    print(analytic_center_hess(A,b)(sol))



