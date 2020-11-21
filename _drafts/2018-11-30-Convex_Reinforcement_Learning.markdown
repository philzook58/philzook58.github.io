---
author: philzook58
comments: true
date: 2018-11-30 00:51:53+00:00
layout: post
link: https://www.philipzucker.com/?p=1506
published: false
slug: Convex Reinforcement Learning
title: Convex Reinforcement Learning
wordpress_id: 1506
---

Pushing the technique up to pong.
To solve the linear program, go interior point. Use Relu weighted penalty method to handle inequalities. Raise weight higher and higher.

Batch with ADMM.
Could choose to throw a neural network in for Q. Ruins all convergence guarantees and convexity, but the basic structure stays the same. Looks like just a slightly weird formulation of Q-learning then. Wasteful? Final relu means that we unnecessarily evaluate Q at points and get little out of it. Could replace with softer penalty function, like exponential. It is nice that we don't have the maximization stage and the fitting stage. Just a single task.
If we stay linear, seems like too many parameters? No weight sharing.

Policy gradient
we want to maximize reward
$latex E[\sum r]$
Or similarly $latex E[Q(s,a)] $
$latex \sum_a\sum_s p(s)\pi(s|a)Q(s,a)$

We estimate the state visitation p(s) via just running the bad boy.
Then we have a BiMatrix problme
$latex \max_\pi \min_Q \pi^T Q$
$latex \pi \ge 0$
$latex \sum_a \pi = 1$
$latex Q \ge r + \gamma Q(t+1) $

Unless I lost a sign there somewhere. Bimatrix games are tractable / convex. Woah, I had forgotten you need the domains to not depend on eahc other. But they don't.

This is a convex analog of an actor critic method. Can use advantage if you like.

By making it proximal, you get

Am I full of crap? Why did we need the pi to stay outside with the log trick in ordinary policy gradient?

There is also the nice thing that from a Q function, we can also use this to get a policy as an LP.



ADMM for batches.





Barnes-Hut / h-matrix / Matrix multiple / Waveletty

Pong is approximately 50,000 input variables let's say. Give or take colors, subsequent time steps.

For an image a full dense linear approximator is feasible. although still quite large. Using square terms is heading towards bad. Big neural networksa do have millions of weights I believe though. Cubes are not looking good.

Howver, what if we use a wavelet style / multiscale deocmposition. We form binary products only for a scale approriate. The fudnamental assumption is that it isn't the correlation of spatially desitnct small details that is necessary, it is the crass behavior at disparate points being correlated. Clearly this can fail, but it can be fixed up in various ways. I feel like this is all a somewhat similar approximation to what a nueral netwrok makes with it's multiscale structure. Weight sharing is a manifestation of translation invariance.We can also reduce the total number of variables using symmettry principles.

We could take a Barnes Hut style sqrt(N) factoring. Use Dsicrete cosine transform inside. Kind of like jpeg.

Could use Wavelet transform.

    
    x = torch.randn(2, requires_grad=True)
    b = torch.tensor([0,0,1.])
    
    A = torch.tensor([[-1.,0]
                     ,[0,-1],
                     [1,1]] )
    
    c = torch.tensor([1.,2.])
    
    
    import torch.optim as optim
    
    # create your optimizer
    optimizer = optim.SGD([x], lr=0.01)
    
    # in your training loop:
    for i in range(1000):
        optimizer.zero_grad()   # zero the gradient buffers
        inequality = A@x - b # Ax < b
        cost = -c@x
        lam = i/100
        loss = cost + lam * torch.sum(F.relu(inequality))
        loss.backward()
        optimizer.step()    # Does the update
    print(x)


Vectorize the cvxpy version - done I think. At least vectorized per episode

How to elegantly deal with the symmettry in



A More traditional Qlearning approahc using cvxpy. Iteratively use cvxpy for function approixmation

Using SOS for maximizing over a. Would introduce 1 SOS variable per constraint. Probably not good.

Small problems : cartpole, pendulum ~5 state variables

Intermediate problems : Byte pong, many jointed robot ~ 100 s variables

Big Problem: Visual pong. 50,000 state variables

Action - in most domains is rather small space. (unless combinatorially large?)

Q(s,a,a,a,a,a) - TD lambda for many a.

Taking the Maxaction is rather slow. Standard Q-learning is a pain. Maybe I just haven't vectorized it enough.

We are kind of doing sarsa.

Using the best action in inequalties is relatively important. That is why discrete sction spaces do well. That's why using the actual action plus a little noise for nearby exploration does well. Plus the totally radom moves gets some exploration.

From this perspective, the SOS for the inequality could be really useful.

The 1 reward seems to work better than the sin(theta) reward? I guess that is quadratic.



    
    import gym
    import numpy as np
    import cvxpy as cvx
    from numpy.polynomial.chebyshev import chebval
    env = gym.make('Pendulum-v0')
    print(env.action_space)
     
    print(env.observation_space)
    print(env.observation_space.high)
     
    print(env.observation_space.low) # [1,1,8]
    print(env.action_space.high) # -2
    print(env.action_space.low)
     
     
    chebdeg = 3
    alpha = cvx.Variable(3*chebdeg**3)
    alpha.value = np.zeros(3*chebdeg**3)
    gamma = 1. - 1./100
    def basis(s,a):
    	n = np.arange(4)
    	f1 = chebval(s[0]/1.,np.eye(chebdeg)).reshape(-1,1,1,1)
    	f2 = chebval(s[1]/1.,np.eye(chebdeg)).reshape(1,-1,1,1)
    	f3 = chebval(s[2]/8.,np.eye(chebdeg)).reshape(1,1,-1,1)
    	f4 = ((a/2)**np.arange(3)).reshape(1,1,1,-1)
    	return f1*f2*f3*f4
     
    def evalb(alpha, s,a):
    	f = basis(s,a)
    	return alpha*f.flatten()
     
    def maxaction(alpha, obs):
        f1 = np.sum(evalb(alpha.value, observation, 2))
        f2 = np.sum(evalb(alpha.value, observation, 0))
        f3 = np.sum(evalb(alpha.value, observation, -2))
        coeff = np.polyfit([2,0,-2], [f1,f2,f3], deg=2)
        if coeff[0] < 0:
        	action = -coeff[1]/2/coeff[0]
        	action = min(max(action,-2),2)
        elif f1 > f3:
        	#print("huh")
        	action = 2
        else:
        	#print("how bout dat")
        	action = -2
        return np.array([action])
     
    constraints = []
    objective = 0
     
     
    
     
    for x in range(4):
     
    	constraints = []
    	observations = []
    	rewards = []
    	actions = []
    	objective = 0
    	epsilon = 1.2/(x+1)
    	print("epsilon: ", epsilon)
    	for i_episode in range(50):
    	    observation = env.reset()
    	    reward = -100
    	    for t in range(100):
     
    	        prev_obs = observation
    	        prev_reward = reward
    	        if np.random.rand() < epsilon:
    	        	action = env.action_space.sample()
    	        else:
    	        	action = maxaction(alpha, observation)
    	        observation, reward, done, info = env.step(action)
    	        observations.append(observation)
    	        rewards.append(reward)
    	        actions.append(action)
    
    	        #constraints.append(evalb(alpha, prev_obs, action) >= prev_reward + gamma*evalb(alpha, observation, action + np.random.randn()*0.2))#maxaction(alpha, observation)))
    	        #objective += evalb(alpha, observation, env.action_space.sample())
    	        if done:
    	            print("Episode finished after {} timesteps".format(t+1))
    	            break
    	bprev = np.array([basis(s,a).flatten() for (s,a) in zip(observations[:-1],actions[1:])])
    	bnext = np.array([basis(s,a+np.random.randn()*0.2).flatten() for (s,a) in zip(observations[1:],actions[1:])])
    	rewards = np.array(rewards)[:-1]
    	constraints = [(bprev@alpha) >= rewards + gamma*(bnext)@alpha]
    
    	bcost = np.array([basis(s,env.action_space.sample()).flatten() for s in observations])
    	objective = cvx.sum(bcost@alpha) # np.sum(bnext,axis=0) * alpha
    	loss = 0.001*cvx.sum(cvx.abs(alpha-alpha.value)) + objective 
    	prob = cvx.Problem(cvx.Minimize(loss), constraints)
    	# The optimal objective value is returned by `prob.solve()`.
    	print("solving problem")
    	result = prob.solve(verbose=True)
    	print(result)
    	# The optimal value for x is stored in `x.value`.
    	print(alpha.value)
    	#inspection loop
    	for i_episode in range(4):
    	    observation = env.reset()
    	    #env.env.state[0] = np.random.randn()*sigma 
    	    for t in range(200):
    	        env.render()
    	        #print(observation)
    	        prev_obs = observation
    	        action = maxaction(alpha, observation)
    	        #print(action)
     
    	        observation, reward, done, info = env.step(action)
    	        if done:
    	            print("Episode finished after {} timesteps".format(t+1))
    	            break




Thoughts on the polynomial spaces and other pieces.

    
    # forming polynomials
    
    #method 1
    
    # multiply factors of all degree < d ->  d^N expoenntial in number of variables
    # tensor product of 1-d spaces
    
    # use only terms of total degree < d ->  N^d expoential in total degree
    # use only terms of weak mixing. total degree < d and total number of variables per term < z. 
    # The interesection of method 1 and method 2
    # Total number of variables per term < z = sum N choose n, n < z. DOminated largely by N!/(N-z)!/z!. < N^z
    
    
    # we want to remove symmettry factors also. 
    
    
    # bad because of symmettries
    def poly(x, d):
       x = np.append(x,1)
       shapes = np.eye(d)
       map(tuple, shape)
       acc = 1
       for i in range(d):
          acc *= x.reshape(shapes[d])
       #power method
       powers = []
       for i in range(log(d))
        x = x.flatten()
        x = x.reshape(1,-1)*x.reshape(-1,1)
        powers.append(x)
       # do powers array
    
    #method 2
    
    
    def poly(x,d):
       x = x.reshape(2,-1) # pair up variables
    
    def powers(d):
       nmk = []
       for n in range(d):
          for m in range(d-n):
             for k in range(d-m-n): #n + m + k < d
                #nmk[n*(d-n)*(d-m-n) + m*(d-m-n) + k, :] = np.array([n,m,k])
                nmk.append((n,m,k))
        return np.array(nmk)
    
    np.prod(x.reshape(1,-1)**nmk, axis=1)
    
    or could we form
    xd = x**range(d)
    xd[nmk] # just access the powers?
    allpoly = x0[n]*x1[m]*x2[k]
    # or a full dynamic rpgoramming solution
    x01 = x0[n]*x1[m]
    x012 = x01[nm]*x2[k]
    # That's pretty good.
    
    
    
    
    
    def poly(x,y,d):
       xy = x[:d].reshape(1,-1) * y[:d].reshape(-1,1)
       xy.flatten() # but in diagonal order.
       #xy = xy[:d,:d]
    
    
    
    #multivariate horner?
    
    #sympy
    def poly(N,d):
    	x = Vector(N+1)
    	.replace(x[0],1)
    
    def wavelet(x, y):
    	N = x.shape[0]
    	if N == 1:
    		return x
    	#y = np.zeros_like(x)
    	y[:N/2] = x[::2] - x[1::2]
    	wavelet(x[::2] + x[1::2], y[N/2:])
    	#return y
    # walsh hadamard
    
    
    def walshhadamard(x):
    	N = x.shape[0]
    	y = np.zeros_like(x)
    	j = N
    	while j > 1:
    		y[:j] = x[j::2] - x[j::2]
    		y[j:] = x[j::2] + x[j::2]
    
    		temp = x
    		x = y
    		y = temp
    
    		j = j/2 
    
    
    
    
    
    
    
    
    
    






Goddamn cylp is a derelict project. Python 2 only. Maybe I would have had more luck installing cbc from souce rather than brew

Needed to manually add a bunch of include files. It seems like the directory structure is off somehow


export CPLUS_INCLUDE_PATH=/usr/local/Cellar/clp/1.16.11/include/clp/coin/:/usr/local/Cellar/osi/0.107.9/include/osi/coin/:/usr/local/Cellar/coinutils/2.10.14/include/coinutils/coin/:/usr/local/Cellar/cbc/2.9.9_1/include/cbc/coin/:/usr/local/Cellar/cgl/0.59.10/include/cgl/coin/


I looked into using Pyomo. Not sure it will work. How do you vectorize stuff? I have little faith in a speedy compilation otherwise.

Gurobi?

I feel like it's possible an lp solver will be faster than OSQP.

If we used localized splines, the constraints would come out sparse. That may help solve time. Each data point would only have a couple nonzero entries. Hmm. That could REALLY help solve time. We could still do the < d scaling N^d rather than the d^N.

Could we throw in some mixed integer for more flexibility?

If we binarized the image, each pixel is only 0 or 1. Then there is no reason to have a higher power than x^1. So it becomes all about N choose d. Which again is roughly N^d.

https://github.com/jjhelmus/CyLP/tree/py3

crossing my fingers here.

installing cylp from source.

cython problems



Disable cython manually in setup.py by setting USE_CYTHON=False

python3 -m cython --cplus CyCbcModel.pyx

python3 -m cython --cplus CyClpSimplex.pyx





    
    s = [N,5]
    
    
    #something like this
    def sdot(s,a):
    sdot = np.zeros_like(s)
    sdot[:,0] = s[:,1]
    sdot[:,1] = a
    sdot[:,2] = - s[:,4] * s[:,3]
    sdot[:,3] = s[:,4] * s[:,2]
    sdot[:,4] = g * sdot[:,2] + a * sdot[:,3]
    return sdot
    
    dt = 0.1
    
    s1 = pts + dt * sdot(pts, F)
    s2 = pts + dt * sdot(pts, -F)
    s3 = pts - dt * sdot(pts, -F)
    s4 = pts - dt * sdot(pts, F)
    
    # could also do a legit odeint. and integrate reward
    # Or do legit finite time horizon Optimal control from grid point.
    #also gives good error estimate. If local action and trjaectory diagree, should refine.
    # also adds a new constraint data point. Could use every point in the trahecotry optimization as a data point. Why throw it away?
    # Well we may want to throw it away if we have to many constraints.
    # kind of a TD(lambda)? The end value of the trajectory optimization may be reaplced with the current value of Q.
    
    
    #Could brute force try every edge in the graph. See which ones don't match up well and bisect them. If they do work well, at least you have a new data point. Is there even a point to the LP anymore? It will just equal the value of the traj opts.
    # really you need to search within the trajectory for bad Q actions not just at the origin.
    # Or just add worst point of trajecotry and re triagnulate.
    # add whole trajectory to constraints. Point with largest dual is the most improtant data point. Add that one.
    
    
    #The point is then generalization/interpolation and speed.
    # we can also may still use MPC but a lighter weight one. With the Q function as a guide, shortened horizon using Q.
    # This hybrid planning and RL is remincent of alpha zero.
    # Could just pre run many traj opts and store them in a table for small enough D.
    
    
    def reward(s):
    return s[:,3] - (s[:,0] / 4)**2
    
    #pure value function version
    
    # To which timestep hsould rewards belong?
    
    # rewards((s1 + pts)/2)?
    
    
    constraints += [basis(pts) * alpha <= reward(pts) + gamma * basis(s1) * alpha]
    constraints += [basis(pts) * alpha <= reward(pts) + gamma * basis(s2) * alpha]
    constraints += [basis(s3) * alpha <= reward(pts) + gamma * basis(pts) * alpha]
    constraints += [basis(s4) * alpha <= reward(pts) + gamma * basis(pts) * alpha] # rewards(s3)?
    objective = cvx.sum(alpha)






The ability to run trajectory optimization and get a ground truth value makes this very different from a laplace problem.

It seems like there are a bunch of ways to mix and match these abilities. The whole thing can be viewed as an overblown lookup table.



Just making sure I understand how Dealuney is working

    
    import scipy.spatial as spatial
    import numpy as np
    
    D = 6
    
    pts = np.zeros((D+1,D))
    for i in range(D):
    	pts[i,i]=1
    
    
    tri = spatial.Delaunay(pts)
    print(tri)
    print(tri.simplices)
    print(pts[tri.simplices])
    print(tri.find_simplex(np.ones(D)*0.1))
    b = tri.transform[0,:D].dot(np.zeros(D) - tri.transform[0,D])
    print(b)
    b = tri.transform[0,:D].dot(np.array([1,0,0,0,0,0]) - tri.transform[0,D])
    print(b)


Find outer simplex? Convert H rep of bounds to V rep. Really want outer simplex though



Is finding which simplex you're in a mixed integer program? There can be many ven for small number of vertices.



    
    N = 200
    pts = np.random.randn((N,D))
    
    tri = spatial.Delaunay(pts)
    
    def sdot(s,a):
       g = 9.8 
       L = 1.0 
       gL = g * L 
       m = 1.0 # doesn't matter 
       I = L**2 / 3 
       sdot = np.zeros_like(s)
       sdot[:,0] = s[:,1]
       sdot[:,1] = a
       sdot[:,2] = - s[:,4] * s[:,3]
       sdot[:,3] = s[:,4] * s[:,2]
       sdot[:,4] = (- gL * s[:,3] + a * L * sdot[:,2])/2 * Iinv
       return sdot
    
    dt = 0.1
    '''
    s1 = pts + dt * sdot(pts, F)
    s2 = pts + dt * sdot(pts, -F)
    s3 = pts - dt * sdot(pts, -F)
    s4 = pts - dt * sdot(pts, F)
    '''
    
    #barycenters = np.sum(pts[tri.simplices.flatten(),:].reshape( pts.shape[0] , D+1 , D), axis=1) / (D+1)
    barycenters = np.sum(pts[tri.simplices,:], axis=1) / (D+1) # an N,D array
    bary = barycenters
    
    s1 = bary + dt * sdot(bary, F)
    s2 = bary + dt * sdot(bary, -F)
    s3 = bary - dt * sdot(bary, -F)
    s4 = bary - dt * sdot(bary, F)
    
    
    def basis(s):
    	simp = tri.find_simplex(s)
    	bary = tri.transform[simp,:D].dot(s - tri.transform[simp,D])
    	I = tri.simplices[simp, :].flatten()
    	J = (np.arange(s.shape[0]).reshape(-1,1) * np.ones(D+1).reshape(1,-1)).flatten()
    	return sparse.lil_matrix(bary, I, J)
    
    
    def V(s):
    	basis(s) * alpha
    
    
    #specializing to baryecenters
    # Eh. Neh. I need to search just in case I exitted the simplex anyhow
    #	Vbary(s):
    
    
    
    V(s4) <= 2*dt*reward(s4) + (np.exp(-2*dt/ T )*V(s1)
    
    posF = V(s4) - (2*dt*reward(s4) + (np.exp(-2*dt/ T )*V(s1))
    negF = V(s4) - (2*dt*reward(s4) + (np.exp(-2*dt/ T )*V(s1))
    
    constraints += [posF >= 0]
    constraints += [negF >= 0]
    
    #objective. Maybe one wants to weight differently.
    # could use stationary distribution. p(s) = p0 + gamma*p(best s), p>0, sum p dx = 1 volume factor
    # or since total probability is convered, use probability flux through simplex faces. sum j = p0
    cvx.sum(V(pts))
    
    #This policy iteration is in totality not a convex process since best s depends on V. Also allows one to put probablistic dynamics in there. Which is nice
    # and pretty cool.
    
    
    #Get all the slack in in order
    #min is because we don't care about the bad action slack.
    
    #maybe pick the worst with a randomness or a Temperature. Helps exploration.
    
    
    
    worst = np.flip(np.argsort(np.min(posF.value(), negF.value())))[:10]
    #maybe we care more about max(V(snext)) -> Slack of snext max.
    # These two things might be roughly the same though.
    
    pts += barycenters[worst,:]
    
    
    # And then iteratively redo.
    
    #But of course, i think the first thing we should do is NOt the iteratvie version. We hsould just sneeze on it and do our best.
    
    # Boundary conditions? I am concerned that it will spend a lot of time exploring here.
    
    #actually rather than the box, a polytopic region makes more sense. A fast right mover at the right edge is very bad. 4 >= x+vt >= 4 and >= v >=
    
    
    
    # reward(s4) + e**(-dt/T)reward(bary) ? A higher order integration of reward
    
    # Since V (and reward) is almost certainly locally linear we could use Kalman control? Maybe not.
    # That would be nice for continuous action choices
    
    
    #We are considering all piecewise constant control schemes.
    
    # for slack, create an expression for the slack and check its value after solve
    
    
    
    #Add points is available. Interesting
    
    









