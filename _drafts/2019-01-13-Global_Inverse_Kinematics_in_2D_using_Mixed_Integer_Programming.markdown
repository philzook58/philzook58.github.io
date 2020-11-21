---
author: philzook58
comments: true
date: 2019-01-13 20:42:51+00:00
layout: post
link: https://www.philipzucker.com/?p=1536
published: false
slug: Global Inverse Kinematics in 2D using Mixed Integer Programming.
title: Global Inverse Kinematics in 2D using Mixed Integer Programming.
wordpress_id: 1536
---

I saw a beautiful sequence of tricks on how to embed an inverse kinematics problem into a Mixed Integer program.

[https://groups.csail.mit.edu/robotics-center/public_papers/Dai17.pdf](https://groups.csail.mit.edu/robotics-center/public_papers/Dai17.pdf)

Inverse kinematics is the problem of finding the angles of a robotics links to put a piece of it where you want it to go.

Rotations are a nasty seeming space to optimize over. The multiplication of rotations matrices is nonlinear and the matrices themselves the orthogonality constraints $latex R^T R = I$.

The typical way you might go about this is to use a local nonlinear solver which is going to basically be some sophisticated version of gradient descent. You have no guarantees that you will find a solution depending on your starting position.

Formulating the problem as an approximate mixed integer convex problem gives better global guarantees.

We can simplify the problem significantly by reducing the problem to 2D. Why not. In 2d, the space of rotations is just a circle.

The first trick is to consider global rotations only, all with reference to the base frame. This means there is no direct multiplication of your matrix variables.

The second

My first inclination to describe the position and orientations of robotic links is to talk about the individual rotation matrices of each link, then composing them by multiplication to get global orientations all the way from the base to the tip and in between.

However, this multiplication process is pretty nonlinear.

The second trick is how to build in .  This also appear to be bad news on a first look.

The position of the n+1 link can be described in terms of the position of the nth link + the rotated vector of the links length $latex t_{n}$.

$latex r_{n+1} = r_{n} + R_{n}t_{n}$

[![](http://philzucker2.nfshost.com/wp-content/uploads/2018/12/9238e574-af16-4d98-bb32-f6f297d35303.png)](http://philzucker2.nfshost.com/wp-content/uploads/2018/12/9238e574-af16-4d98-bb32-f6f297d35303.png)

If you want to optimize over a circle $latex x^2 + y^2 = 1$, that is a non convex region, which means you can't use a straight convex solver. The filled in circle $latex x^2 + y^2 \le 1$ is a convex region, so that is fine.

More generally, you can take a nonconvex constraint and use it's convex hull instead as a relaxation. If the nonconvex constraint is the boundary of a convex region, you can use the mixed integer union of secant planes pushing outward to cut out the bulk of the interior.

We can approximate a convex outer region by a bunch of tangent planes of the region. This may be desirable if you don't have anything except a linear programming solver, but it is getting fishy. Do the tractable parts as exactly as you can.

One great thing about this formulation is that it becomes easy to put constraints on the robotics pose such as "no link can go through the floor", or solve for non tree like robotic link configurations.

On the downside, you probably need a local gradient/newton solver like Ipopt in addition to this to clean up the solution, due to the roughness of of the approximation.

An important trick in Mixed Integer programming is the "Big-M" trick. What it does is it let's you build an interface between the binary world and the continuous world that lives in mixed integer programming, i.e. let a binary variable control whether a linear constraint is on or off. Given some constraint $latex \phi(x)\le 0$, you can add a term $$latex \phi(x)\le M z$. If z=0, then the constraint is exactly as it was before. If z=1 with $latex M=\infinity$ , then the constraint is not constraining at all. In actuality we need to pick a finite but sufficiently large M such that when z=1, then constraint still doesn't matter. How big this M has to be is context dependent. While any M larger than a threshold is correct, using the smallest value of M that makes the constraint irrelevant when z=1 will tend to aid the mixed integer search process (the linear relaxation should be as tight as possible). We already have a solver available to find this M luckily. If we flip the constraint and set z=1,  $latex \phi(x)\ge M$. $latex M \ge 0$ with the other available constraints for our original problem and the make the objective $latex \max M$, it will find the minimum value of M that makes the constraint irrelevant. We can add a small margin (1% let's say) to the value of M just to be safe against numerical issues and then use it.

A related possibility is to  use interval arithmetic. If we already have upper and lower bounds on all the variables, then we can use interval arithmetic to establish a sufficient M value.

    
    import cvxpy as cvx
    import numpy as np
    
    
    x = cvx.Variable(2)
    c = []
    
    N = 10
    thetas = np.linspace(-np.pi, np.pi, 10)
    z = cvx.Variable(N,boolean=True)
    for theta in thetas:
    	# use tangent plane of constraint
    	c += [(x[0] - np.cos(theta))  * -np.sin(theta) + (x[1] - np.sin(theta)) * np.cos(theta) <= 1]
    	
    #c += [x <= 1, x >= -1] #outer square
    
    
    for i in range(-1,N-1):
    	#use secants
    	x1 = np.cos(thetas[i])
    	y1 = np.sin(thetas[i])
    	x2 = np.cos(thetas[i+1])
    	y2 = np.sin(thetas[i+1])
    	c += [  (x[1] - y1)(x1 - x2) - (x[0] - x1)(y1 - y2)  + 10*z[i]  ]
    
    c += [x[0]+x[1] >= 1 - 10*z[0]]
    c += [-x[0]-x[1] >= 1 - 10*z[1]]
    c += [x[0]-x[1] >= 1 - 10*z[2]]
    c += [-x[0]+x[1] >= 1 - 10*z[3]]
    
    
    
    objective = cvx.Maximize(x[0]+x[1])
    constraints = c
    
    prob = cvx.Problem(objective, constraints)
    res = prob.solve(solver=cvx.CBC, verbose=True)
    
    
    print(x.value)


http://groups.csail.mit.edu/robotics-center/public_papers/Dai17.pdf

Applications to quantum control

Arbitrary Lie Groups?

A convex surface. It is combinig the convex hull of the surface pullinh in with the secant planes  pushing out

    
    import cvxpy 
    
    
    
    #2d robotics global optimization
    
    class Link():
       def getR(self):
    
       def getT(self):
    
    class AngleLink(Link):
    	self.angle = 0
    	self.c = cvx.Variable(1)
        self.s = cvx.Variable(1)
        self.cpos = cvx.Variable(1)
        self.cneg = cvx.Variable(1)
        constraints += [self.cpos - self.cneg == self.c]
        self.hor = cvx.Variable(1, binary = True)
        constraints += [self.cpos >= 0, self.cpos <= self.hor]
        constraints += [self.cneg >= 0, self.cneg <= self.hor]
        constraints += [c
    
        #indicator vairables
        z = cvx.Variable(4, binary = True)
        cs = cvx.Variable(4)
        ss = cvx.Variable(4)
        c  = cvx.sum(cs)
        s = cvx.sum(ss)
        constraints += [0 <= cs[0], cs[0] <= z[0], 0 <= -cs[1], -cs[1] <= z[1], 0 <= -cs[2], -cs[1] <= z[2], 0 <= cs[3], cs[3] <= z[3]]
        M = 1 + np.sqrt(2)+0.001
        # the zs turn on or off the different constraints
        # in prnciple we hsould only need 2 z
        # secant line suppression
        constraints = [c + s >= 1 - 3*z[0], c - s >= 1 - 3*z[1], -c - s >= 1 - 3*z[2], - c - s >= 1 - 3*z[3]] #Tightest value M = 1 + sqrt(2)
        constraints += [cvx.sum(z) == 1]
        constraints += [c**2 + s**2 <= 1]
    
        thetas = np.linspace(-np.pi, np.pi, 4)
        cs = np.cos(thetas)
        cdiffs = cs - cs[-1:] # off by 1. annoying
        sdiffs = 
        ss = np.sin(thetas)
        # according to wikipedia
        sdiffs*xs + cdiffs*ys >= cs[:-1]*ss[1:] - cs[1:] - ss[:-1]
           >= 1 - 3
    
    
    
        self.constraints = [c**2 + s**2 <= 1]
        '''
        self.hor = cvx.Variable(1, binary=True)
        self.vert = cvx.Variable(1, binary=True)
        self.constraints += [c <= self.hor, -(1 - self.hor) <= c ]
        self.constraints += [s <= self.vert, -(1 - self.vert) <= s ]
        self.constraints += 
        '''
    	def getR():
    
    class OffSetLink(Link):
    	self.offset = np.zeros(2)



    
    '''
    The ideal physics engine would
    1. run imperatively if need be
    2. be differentiable if need be
    3. output mathematical programs if need be
    
    Thoughts:
    State monad vs some kind of MP monad
    FRP 
    
    Julia, python, haskell
    
    Could just output to cvxy vs pymunk vs pytorch.
    
    '''
    
    
    class CvxObj():
    	constraints = []
    
    
    
    
    class World():
    	# Bounding the world significantly eases big M problems
    	self.Lx = 100	
    	self.Ly = 100
    	def build_problem(self, obj, timesteps, dt):
    		for t in times:
    			for body in bodies:
    				body.update_v()
    			for body in bodies:
    				body.update_x()
    		cvx.problem(obj, [body.constraints for body in self.bodies] )
    
    
    
    class Body():
    	self.static = False
    	self.kinematic = True
    	self.kinfun = lambda t: 2 * t + 4
    	self.shape
    	self.collision = 
    	def update_v(self, dt):
    		vnew = cvx.Variable(2)		
    		self.constraints(vnew == self.v + dt * self.ext_force)
    		vproj = vnew
    		for joint in self.joints:
    			vproj = joint.project_v(vproj)
    		self.v = vproj
    
    def flip(z):
    	return 1-z
    
    def reifyPlanes(A,b,x): #x is point variables
    	M = 100
    	z = cvx.Variable(b.size, binary=True)
    	A*x + M*z >= b #if z is 1, this is relaxed
    	A*x <= b + M*flip(z) # if z is 0 this is relaxed
    	# hence z = 1 => Ax <= b, z = 0 implies Ax >= b
    
    
    #make everything work with the "Dual Number" that packages toegther constraints and variables.
    #hopefully preprocessing will rmove redundancy
    
    #store process graph like Reverse mode ad.
    
    class ConstrVar():
    	def __init__(size):
    		self.var = cvx.Variable(size)
    		self.constraints = []
    	def __eq__(self, b):
    		self.constraints += [self.var == b]
    
    # expressions that carry constraint environment
    class ConstrExpr():
    
    class ConstrObj():
    
    class ConstrVar(cvx.Variable):
    	def __init__(self, size):
    		#self.var = cvx.Variable(size)
    		self.constraints = []
    		self.var = super(size)
    	def __eq__(self, b):
    		self.constraints += [self.var == b]
    		# Or reify by default?
    		z = ConstrVar(Boolean)
    		 z * M yadaya
    		 return z 
    	def __le__(self,b):
    		# reify by default?
    	def assert(self, cond):
    		#direct assertion of properties
    		self.constraints += cond(self.var)
    
    
    def conditionalPlane(z, A,b,x): # if z is 0, then Ax=b, otherwise we don't care
    	-M * z <= A*x - b <= M z
    def conditionalIneq(z, A,b,x): # if z is 0, then Ax=b, otherwise we don't care
    	A*x - b <= M z # turn off inequality
    
    # I feel like many of these are overlapping 
    
    # reify expr is >= 0
    boxconstraints = [ x <= 10, -10 <= x, etc. ]
    
    
    
    # Puts a condition constraint on expr. if z == 1, then expr <= 0. if z == 0, no conclusion.
    # is a binary implication z implies (expr <= 0)
    
    def impliesPos(expr , contextConstraints):
    def impliesPos(z, expr , contextConstraints): # could have the boolean variable supplied rather than generating it
    
    def mexpr(expr, constraints):
    	obj = cvx.Maximize(cvx.max(expr))
    	cvx.prob(obj, constraints).solve() # or maybe with timeout and take upper bound. This allows us to use boolean constraints
    	M = expr.value + 1 # just to be safe.
    	z = cvx.Variable(1, binary=True)
    	return z, M, expr <= M*(1-z) # new constraint. if z = 1, expr <=0, else expr <= M and M is larger than maximum possible value of expr.
    
    
    
    def reifyPlane(A,b,x, constraints): #reifies inlcusion in polygon defined by Ax <= b
    	expr = A*x-b
    	z1, M1, c1 = mexpr(expr, constraints)
    	z2, M2, c2 = mexpr(-expr, constraints)
    	return z1, [c1, c2, z1 == 1 - z2]
    # reify plane is also how one mightb perform if(Ax<=b): else: in an new execution context. reify plane is the return of the comparison operator.
    
    # reify plane is how to convert a plane test to a boolean value
    #mexpr is how to convert a bool into an inequality
    # refiy plane is how to convert bool into a equality constraint? M (1-z) <= x  <= Mz is posQ
    
    # -Mz <= x <= Mz
    # is enforced equaltiy constraints.
    
    
    def depEq(z, expr, constraints):
    	z1, M1, c1 = mexpr(expr, constraints)
    	z2, M2, c2 = mexpr(-expr, constraints)
    	return z1, [c1, c2, z1 == z2]
    
    def abstract(expr, constraints): # returning both z1 and z2 without applying anything extra seems to cove both posQ and dependeant equality
    	z1, M1, c1 = mexpr(expr, constraints)
    	z2, M2, c2 = mexpr(-expr, constraints)
    	return z1, z2, [c1, c2]
    
    def posQ():
    
    def depEq(z, expr):
    	z1,z2, cs = abstract(expr, constraints)
    	return cs + [z1 == z2, z == z1]
    
    def ITE(z, expr1, expr2):
    	depEq(z, expr1)
    	depEq(zNot(z), expr2)
    
    
    
    def reifyPolygon(A,b,x,constriants):
    	expr = A*x-b
    	z1, M1, c1 = mexpr(expr, constraints)
    	q = [mexpr(-row, constraints) for row in expr]
    	zs = [z  for (z,M,c) in q ]
    	cs = [c  for (z,M,c) in q ]
    	return z1,  cs + [z1 == 1 - zAnd(zs)]
    
    
    #piecwise linear functions are easiest to express in a triangulated domain
    # SOS generalizes to one suppression vairable per face, one interpolation variable per vertex.
    # 
    
    #Hmm. Maybe refiyPlane should be split into two things. Just a is x<=0 e>= 0 test
    def posQ(x,constraints):
    	 z1, _, c1 = mexpr(x, constraints)
    	 z2, _, c2 = mexpr(-x, constraints)
    	 return z1, [c1, c2, z1 == 1 - z2]
    
    def relu(x,constraints):
    	z, cs = posQ(x)
    	y = cvx.Variable(1)
    	ITE(z, y - x, y) # if x is positive, y = x, else y = 0
    	return y, 
    
    def relu2(x):
    	xplus = cvx.Variable(1)
    	z = cvx.Variable(1, binary=True)
    	#zminus = cvx.Variable(1, binary=True)
    	xminus = cvx.Variable(1)
    	x == xplus - xminus
    	xplus >= 0
    	xminus >= 0
    	xplus <= M*z
    	xminus <= M*(1-z) # only one at a time
    
    	# Russes paper has a different encoding
    
    
    	return xplus
    
    def relu3(x): # The way tedrake does it
    
    def piecewise(xs, f):
    	def g(x):
    
    	return g
    
    
    # a very nasty way of threading all these constraints. Just put the @gc decorator on top of all constraint returning functions.
    # this is the writer monad style.
    def gc(f): #gloabl constraints combinator. Pass on parameters, throw constraints into gloabl pile and pass on results.
       global constraints
       def temp(*args):
       		res = f(*args)
       		constraints += res[-1]
       		return res[:-1]
       return temp
    
    
    
    
    def zAnd
    def zOr
    def zXor
    def zNot
    
    
    def polyIntersect(A1,b1,A2,b2)
    
    
    def existsQ()
    	var1 = cvx.Variables()
    	z1 = poly1(var1)
    	z1 == True
    	var2 = cvx.Variables()
    	z2 = poly2(var2)
    	z2 == True
    	-Mz <= var1 - var2 <= Mz
    	# Min z? But in a way to not screw up other objectives. Min D*z where D is bigger than largest possible objective?
    
    def forallQ():
    
    #another wyat o test collision:
    # take a vertices of polygon and use point polygon collision
    
    def pointInPolygon(A,b,x):
    	res = reifyPlanes(A,b,x)
    
    
    
    
    
    
    # axis alignement isn't gonna save us much
    # many collision detection things 
    class AABB():
    	def __init__(x,y,x0,y0,w,h):
    		reifyPlane()
    	z
    class CollisionPolygon():
    
    
    
    class CollisionCircle()
    
    
    class Joint():
    
    
    class Shape(): 
    
    
    class IntrinsicBody():
    	def jacobian
    
