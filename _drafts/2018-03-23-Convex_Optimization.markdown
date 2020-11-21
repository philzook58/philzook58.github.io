---
author: philzook58
comments: true
date: 2018-03-23 13:46:49+00:00
layout: post
link: https://www.philipzucker.com/?p=1004
published: false
slug: Convex Optimization
title: Convex Optimization
wordpress_id: 1004
---

One thing that was emphasized is that there may be great benefit to writing your own convex solver since general purpose ones may not exploint linear algebraic structure (diagonal, low rank, triadiagonal, triangular, fft, etc)

So here is a start

    
    import numpy as np
    from scipy import linalg
    
    # I should rewrite my LQR solver in the lagrange form. It's very reasonable and if i use banded, very fast.
    
    # If is composition of Ax+b then there is a slight optimizatiomn that can be performed for backtracking
    def linesearch(f, df0, x, dx, alpha=0.25, beta=0.1):
    	f0 = f(x)
    	t = 1
        while f(x + t * dx) > f0 + alpha * t * df0 @ dx:
        	t *= beta 
        return t
    
    def newton(f, x0, grad, hessInv):
    	while True:
    	    df = grad(x)
    	    dx = - hessInv(df)
    	    newton_decrement = - df @ dx
    	    t = linesearch(f, df, x, dx)
    	    x += t * dx 
    	    if newton_decrement / 2 < 1e-10:
    	      return x  
    
    def interiorPoint(f, x, grad, hessInv, phis, gradphis, hessPhis):
    	def gradB(x,t): 
    		return t * grad(x) - (grad phi) / phi(x)
    	def HessInvB(x,t):
    		# use low rank update. Assumes that less inequality constraint than 
    	t = 1
    	while True:
    		x = newton(f, x gradB(t), hessInvB(t))
    
    
    		if gap < 1e-10:
    			break
    		t *= 10
    
    def blocksolve(Ainv, B, C, D, b0, b1): # Ainv is in functional form
    	'''
    	Ainv is called multiple times.
    	Precompute any factorizations that may help that (or memoize them)
    	D is small
    	A B | x0 = b0
    	C D | x1 = b1
    	'''
    	#b1 -= C @ Ainv(b0)
    	x1 = linalg.solve(D - C @ Ainv(B), b1 - C @ Ainv(b0) )
    	x0 = Ainv(b0 - B @ x1)
    	return x0, x1
    
    #Look in Strang. He may indeed have already had these algorithms in this form
    def gauss(A):
    	n = A.size[0]
    	U = np.copy(A)
    	L = np.zeroeslike(A)
    	pivots = []
    	while n > 0:        
            pivot = np.argmax(U[:,0])
            pivots.append(pivot)
            swap(U[pivot,:], U[0,:])
            L[0,0] = 1
            L[:,0] = - U[:,0] / U[0,0]
            U[1:,:] += U[0,:].reshape(1. -1) * L[:,0].reshape(-1,1) 
            U = U[1:,1:]
            L = L[1:,1:]
    		n--
    	return L, U, pivots
    
    def householderQR(A):
    	reflectors = []
    	while n > 0:
    		x = np.copy(A[:,0])
    		#	e = np.zeroslike(x)
    		norm2 = np.linalg.norm(x[1:])
    		x[0] -= np.sqrt(norm2 + x[0]**2)
    		x = x / (np.sqrt(norm2 + x[0]**2))
    
    		reflectors.append(x) 
    		A -=  2 * v.reshape(-1,1) * (v @ A).reshape(1,-1)
    		n--
    	return reflectors, A
    
    def hessenberg(A):
    	reflectors = []
    	while n > 1:
    		x = np.copy(A[:,0])
    		x[0]=0
    		#	e = np.zeroslike(x)
    		norm2 = np.linalg.norm(x[2:])
    		x[1] -= np.sqrt(norm2 + x[1]**2)
    		x = x / (np.sqrt(norm2 + x[1]**2))
    
    		reflectors.append(x) 
    		A -=  2 * v.reshape(-1,1) * (v @ A).reshape(1,-1)
    		A -=  2 * (A @ v).reshape(-1,1) * v.reshape(1,-1)
    		n--
    	return reflectors, A
    
    
    




Ok.

So I've been investiagting for the purposes of trajectory optimization. And I'm in the weeds.



 	
  1. Write equations of motion : By hand. Use symbolic packages?

 	
  2.  Maybe initilize with a heuristic path (perhaps lyapunov based?)


3. Form gradients and hessian. Result will be banded

3.5 Form direct collocation of equations using convex approximation.

4.optimize.

5. go back to 3 until convergence

The resulting

scipy has a sqp solver in it, but it takes dense matrices

scipy also has newton-cg solver which takes sparse matrices. sparisty is acceptable. BUt matrices are actually banded, which may be convenient.

Could use own interior point method. Seems insane.

We need constraints on total applyable power and region boundaries. Manualy form lagrangian?

pytorch has gradient finders in it. Also can form Gradient hessian products?

cxvpy is extremely easy to use. Makes Has sparse solver I believe powering it. but no special support for QP.

Ok. So fastest path to something that could work. Do not write own solvers.

1. get equations of motion

2. write in collocation form

3. get derivatives and hand off to scipy optimize sqslp

4. if that is garbage or slow, get drivatives and write qudratic approximation collocation to cvxpy

Actually I only need the gradients of the equations of motion.

This is very useful. order of magnetidue benchmarks

https://scaron.info/blog/quadratic-programming-in-python.html

jeez. I dunno. If I have to run a couple instances... I have 4 parameters maybe per time steps 100 time steps... No we should be ok.

oh jeez cvxopt has a qp solve function. Is that better?

Getting gradients:

Do by hand or Ask sympy or ask pytorch. I'd need the hessian of the Hamiltonian for linear approximation. Do by hand is easiest.

put acceleration in equations of motion but add constraint that derivative of v is a and that |v| < 2m/s and |a| < ? and  0<x<1

I should use the equations of motion from my article.

I should be using distance squared from the top position as my cost. Gives more weight to good stabilizaition at the top

I guess take the collocation coefficients from that summary paper.

cvxopt has support for using a fast solve. but don't look at that now.



A[2,3,lookead]. only needs to be mat mul on the 3.

Enum helpers

CONTROL = 0

STATE = 1

Even the traperzoidal method might improve my stability

CVXPY makes the solve step of that easy even if not in pushforward form.

Do we want the full







Russ is saying that you want to make sure your cost function always goes down when you're approximating it.

Linear programming for optimal control on a grid?  J(s_i) is cost to go.

If you fill in the connectivity matrix and the thing is detemirnsitc yoiu get a transition matrix T of ones and zeros. g is then the cost of being in state for one time step

J = g + TJ

Then you could still have a nonlinear interpolator functions even on a grid.

J = sum alpha phi(s)

the restriction that J(t+1) < J(t). I think the point here is that you can put one inequality per action choice. The one that will be staturated will be the best action. Is this connected to the fact that a minimum path problem can be written as a linear program?

Robustness: Can put in the inequality contraint for mutiple sets of possible dynamics

http://underactuated.csail.mit.edu/underactuated.html?chapter=dp

Huh. So you optimize for some vector   c dot J that weights performance in different regions subject to the contraint that the J function is decreasing according to the update equation. Interesting.

Woah. Lecture 8 man.

So for a linear dynamical system xdot = A x, stability means that it has all negative eigenvalues.

But to get a Lyapunov function V = xPx that verifies that only needs it to be decreasing with time and also convex?.

http://underactuated.mit.edu/underactuated.html?chapter=lyapunov

https://en.wikipedia.org/wiki/Lyapunov_equation

Huh. The Lyaponuv equation is kind of like the tiem derivative of an operator is quantum mechanics. The commutator is replaced by (Atrans * P + P * Atrans). If we used the complex inner product and if A = iH, then they are the same (since they are coming from the same place.). Is the interaction (Dirac) representation useful?

The common lyapunov system. Require the same lyapunov function works for multiple systems.

The nonlinear trick, you can estimate nonlinear functions with leasts squares. Vandermonde matrices and such.

Likewise, you can make the lyapunov a quadratic form in some funky space.

Sum of Squares polynomials. Some polynomials can be written as a sum of square. (I wonder if there is any advantage to working in the chebyshev basis. It tends to be the right one.) Finding the eigenbasis gives you the sum of squares representation of the polynomial. If the eigenvalues are all positive, then that shows the polynomial is always positive.

converting from alpha dot xn to xn Q xn is a linear equation solving Q in terms of alpha. Actually finding the sum of squares is the harder eigenpoblem. Chebyshev polynomials have some convenient relations for multplication ![2T_{m}(x)T_{n}(x)=T_{m+n}(x)+T_{|m-n|}(x)](https://wikimedia.org/api/rest_v1/media/math/render/svg/aa31a2d6b969f201efbf78e49e1d126a8bc6ca14)



ordinary I'd linearly paramtrize polynomials as alpha dot xn. But for this purpose, alpha is a matrix and we have xn alpha xn. maing alpha positive definite gives a proof that the polynomial stays positive for all x. I don't think the xn have to be polynomials to push that through. I guess this the higher dimensional version of parametrizing a * x^2.

What does polynomials get us? Easy multiplication? Vdot = xn Q dxn/dt. We need closure? Do we actually get it? It's not that dxn/dt ~ A xn right? It's actually that xn Q dxn = xn ~Q xn. I feel like sines nad cosines might be ok. Write them as complex exponentials. Then they close real good.

We have access to polynomials of degree 2n in principle. dxn/dt is gonna have terms n -1 + degree of xdot eq of motion. So recompress xn Q dxn to alpha xn form then decompress to ~Q form. Those will linear constraints between ~Q and Q

https://en.wikipedia.org/wiki/Sum-of-squares_optimization



Coin-Or

What is linear programming for?

Convex Geometry seems very Categorical. Got some notion of inequalities. Thta's nice

class ConvexSet a b where

point :: b -- Gives us an arbitrary point

inSet :: b -> Bool

LevelSet () -- set given by f < 0 --

BoolSet -- set given by f = True

Epigraph -- set given by area above y = f

Can find area of Convex set by using refined convex hull and dual hull. Gives a double sided bound.





NonDecreasing = a -> Double   -- category or operad

Affine -- composable

NonDecreasingConvex



How do generalizedi neqaulities compose for different cones? y -x in K, z - y in K' then z - x in (K+K'). K includes the origin. I think this is the Minkowski sum of the cones? Is the minkwosk sum of cones a cone? Yes. I think so. Given a point, it is the sum of the other points. It might also be the union of the cones. Nope. consider cones pointing in different directions.

Minkowski sum of a cone with itself is itself.

Minimum of function is minimal with respect to cone that is positive y half space.

Convex sets have functions between them

ConvexFun :: (ConvexSet a) => a -> Double

Give COnvex Fun a cute infix notation like ==> or something

Gives axiomatic primitives

and combinators.

Norms are convex (max, lp norms, )

some primitive R -> R functions (log, exp, x log x, powers, )

Rn domaain : max, sum,  (many or all of these are examples of the composition rules)

Convex -> NonDecreasingConvex  -> Convex

Affine -> COnvex -> Convex



Duality? and negation.



The composability notion is very similar to automatic differentiation (not surprising given that for differentiable functions convexity is written as a condition on dervatives).

Traversable t => t Double -> Double





Books to check out:





# Numerical Optimization (Springer Series in Operations Research and Financial Engineering) 2nd Edition







by  [Jorge Nocedal](https://www.amazon.com/s/ref=dp_byline_sr_book_1?ie=UTF8&text=Jorge+Nocedal&search-alias=books&field-author=Jorge+Nocedal&sort=relevancerank) (Author),‎  [Stephen Wright](https://www.amazon.com/s/ref=dp_byline_sr_book_2?ie=UTF8&text=Stephen+Wright&search-alias=books&field-author=Stephen+Wright&sort=relevancerank) (Author













# Approximate Dynamic Programming: Solving the Curses of Dimensionality, 2nd Edition (Wiley Series in Probability and Statistics) Hardcover – September 27, 2011







by  [Warren B. Powell](https://www.amazon.com/Warren-B.-Powell/e/B001IOBOLQ/ref=dp_byline_cont_book_1) __ (Author)










# Dynamic Programming and Optimal Control (2 Vol Set) 4th Edition







Nonlinear Programming: 3rd Edition




Dimitri Bertsekas







Introduction to Linear Optimization (Athena Scientific Series in…




[Dimitris Bertsimas](https://www.amazon.com/Dimitris-Bertsimas/e/B001HD1YP4/ref=pd_sim_14_bl_8?_encoding=UTF8&pd_rd_i=1886529191&pd_rd_r=8WZNP92CC6KMG4C5K1MY&pd_rd_w=2DfET&pd_rd_wg=BlhFh&refRID=8WZNP92CC6KMG4C5K1MY)










Decision Making Under Uncertainty: Theory and Application (MIT Lincoln…




Mykel J. Kochenderfer







# Combinatorial Optimization: Algorithms and Complexity (Dover Books on Computer Science)










# Optimal Learning 1st Edition







by  [Warren B. Powell](https://www.amazon.com/Warren-B.-Powell/e/B001IOBOLQ/ref=dp_byline_cont_book_1) __ (Author),‎  [Ilya O. Ryzhov](https://www.amazon.com/s/ref=dp_byline_sr_book_2?ie=UTF8&text=Ilya+O.+Ryzhov&search-alias=books&field-author=Ilya+O.+Ryzhov&sort=relevancerank) (Author)













# Markov Decision Processes: Discrete Stochastic Dynamic Programming 1st Edition







by  [Martin L. Puterman](https://www.amazon.com/Martin-L.-Puterman/e/B001HP8FHC/ref=dp_byline_cont_book_1) __ (Author)
























