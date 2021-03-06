---
author: philzook58
comments: true
date: 2018-10-14 23:26:23+00:00
layout: post
link: https://www.philipzucker.com/model-predictive-control-of-cartpole-in-openai-gym-using-osqp/
slug: model-predictive-control-of-cartpole-in-openai-gym-using-osqp
title: Model Predictive Control of CartPole in OpenAI Gym using OSQP
wordpress_id: 1369
tags:
- cartpole
- control
- mpc
- openai gym
- osqp
- python
---

A continuation of this post [http://www.philipzucker.com/osqp-sparsegrad-fast-model-predictive-control-python-inverted-pendulum/](http://www.philipzucker.com/osqp-sparsegrad-fast-model-predictive-control-python-inverted-pendulum/)

I was having difficulty getting the model predictive control from a previous post working on an actual cartpole. There are a lot more unknown variables in that case and other issues (the thing has a tendency to destroy itself). I was kind of hoping it would just work. So I realized that I should get it working in simulation.

I did not copy the simulation code of the openai cartpole [https://github.com/openai/gym/blob/master/gym/envs/classic_control/cartpole.py](https://github.com/openai/gym/blob/master/gym/envs/classic_control/cartpole.py)  which gives some small amount of credence that the MPC might generalize to a real system.

For the sake of honesty, I'm still at the point where my controller freaks out about 1/3 of the time. I do not really understand why.

﻿

Your browser does not support the video tag.




Looks damn good here though huh.

A problem I had for a while was the Length of my pole was off by a factor of 2. It still kind of worked, especially if nearly balanced (although with a lot of oscillation, which in hindsight was a clue something wasn't tuned in right).

There are some useful techniques for manipulating gym. You can set some parameters from the outside, like starting positions and thresholds. Also you can mangle your way into continuous force control rather than just left right commands (wouldn't it be cool to use Integer programming for that? Silly, but cool).

There is still a bunch of trash in here from me playing around with parameters. I like to keep it real (and lazy).

    
    import gym
    from mpc import MPC
    import numpy as np
    env = gym.make('CartPole-v0')
    env.env.theta_threshold_radians = np.pi * 2
    env.env.x_threshold = 5 
    
    start_theta = 0#-np.pi + 0.4# + 0.1#2 * np.pi #np.pi+0.4
    
    mpc = MPC(0.5,0,start_theta,0) 
    action = 0
    for i_episode in range(1):
        observation = env.reset()
        env.env.state[2] = start_theta - np.pi
        for t in range(500):
            env.render()
            #print(observation)
            #action = env.action_space.sample()
            observation, reward, done, info = env.step(action)
            a = mpc.update(observation[0] + 0.5, observation[1], observation[2]+np.pi, observation[3])
            env.env.force_mag = abs(a) #min(100, abs(a))
            #print(a)
            if a < 0:
            	action = 0
            else:
            	action = 1
            if done:
            	pass
                #print("Episode finished after {} timesteps".format(t+1))
                #print(observation)
                #print(dir(env))
                #break
    print(mpc.calcQ().reshape((5,50)))
    print(observation)
    print(dir(env))


One problem was that originally I had the pole just want to go to pi. But if it swings the other direction or many swings, that is bad and it will freak out. So I changed it to try to go the the current nearest multiple of pi, which helps.

Fiddling with the size of the regulation does have a significant effect and the relative size of regulation for x, v, f, omega. I am doing a lot of that search dumbly. I should probably do some kind of automatic.

Loosening the constraints on v and x seems to help stability.

I think weighting the angle at the end of the episode slightly more helps. That's why I used linspace for the weight on the angle.

I've had a lot of problem with the answer coming back as infeasible from OSQP. I feel like it probably shouldn't be and that is the solver's problem?

Two things help: sometimes the cart does go out of the allowable range. The optimization probably will try to go all the way to the boundaries since it is useful. And since there is some mismatch between the actual dynamics and my model, it will go outside. So I heavily reduce the constraints for the first couple time steps. It takes a couple. 4 seems to work ok. It should want to apply forces during those four steps to get it back in range anyhow.

Even then it still goes infeasible sometimes and I don't know why. So in that case, I reduce the required accuracy to hopefully at least get something that makes sense. That is what the eps_rel stuff is about. Maybe it helps. Not super clear. I could try a more iterative increasing of the eps?

[https://groups.google.com/forum/#!topic/osqp/BzEqWQR2dYY](https://groups.google.com/forum/#!topic/osqp/BzEqWQR2dYY)



    
    import sparsegrad.forward as forward
    import numpy as np
    import osqp
    import scipy.sparse as sparse
    
    
    class MPC():
    	def __init__(self, x0, v0, theta0, thetadot0):
    		self.N = 50
    		self.NVars  = 5
    		T = 8.0
    		self.dt = T/self.N
    		dt = self.dt
    		self.dtinv = 1./dt
    		#Px = sparse.eye(N)
    		#sparse.csc_matrix((N, N)) 
    		# The three deifferent weigthing matrices for x, v, and external force
    		reg = sparse.eye(self.N)*0.05
    		z = sparse.bsr_matrix((self.N, self.N))
    		# sparse.diags(np.arange(N)/N)
    		pp = sparse.diags(np.linspace(1,7,self.N)) # sparse.eye(self.N)
    		P = sparse.block_diag([reg, 10*reg ,pp, reg, 10*reg]) #1*reg,1*reg])
    		#P[N,N]=10
    		self.P = P
    		THETA = 2
    		q = np.zeros((self.NVars, self.N))
    		q[THETA,:] = np.pi
    		q[0,:] = 0.5
    		#q[N,0] = -2 * 0.5 * 10
    		q = q.flatten()
    		q= -P@q
    		#u = np.arr
    
    		self.x = np.random.randn(self.N,self.NVars).flatten()
    		#x = np.zeros((N,NVars)).flatten()
    		#v = np.zeros(N)
    		#f = np.zeros(N)
    
    
    		#print(f(ad.seed(x)).dvalue)
    
    
    
    
    		A, l, u = self.getAlu(self.x, x0, v0, theta0, thetadot0)
    		self.m = osqp.OSQP()
    		self.m.setup(P=P, q=q, A=A, l=l, u=u , time_limit=0.1, verbose=False)# , eps_rel=1e-2 #  **settings # warm_start=False, eps_prim_inf=1e-1
    		self.results = self.m.solve()
    		print(self.results.x)
    		for i in range(100):
    			self.update(x0, v0, theta0, thetadot0)
    
    	def calcQ(self):
    		THETA = 2
    		q = np.zeros((self.NVars, self.N))
    		thetas = np.reshape(self.x, (self.NVars, self.N))[THETA,:]
    		thetas = thetas - thetas % (2*np.pi) + np.pi
    		q[THETA,:] = thetas[0] #np.pi #thetas
    		q[0,:] = 0.5
    		#q[N,0] = -2 * 0.5 * 10
    		q = q.flatten()
    		q = -self.P@q
    		return q
    
    	def update(self, x0, v0,theta0, thetadot0):
    		A, l, u = self.getAlu(self.x, x0, v0, theta0, thetadot0)
    		#print(A.shape)
    		#print(len(A))
    		q = self.calcQ()
    		self.m.update(q=q, Ax=A.data, l=l, u=u)
    		self.results = self.m.solve()
    		if self.results.x[0] is not None:
    			self.x = np.copy(self.results.x)
    			self.m.update_settings(eps_rel=1e-3)
    		else:
    			#self.x += np.random.randn(self.N*self.NVars)*0.1 # help get out of a rut?
    			self.m.update_settings(eps_rel=1.1)
    			print("failed")
    			return 0
    		return self.x[4*self.N+1]
    
    
    
    	def constraint(self, var, x0, v0, th0, thd0):
    		#x[0] -= 1
    		#print(x[0])
    		g = 9.8
    		L = 1.0
    		gL = g * L
    		m = 1.0 # doesn't matter
    		I = L**2 / 3
    		Iinv = 1.0/I
    		dtinv = self.dtinv
    		N = self.N
    
    		x = var[:N]
    		v = var[N:2*N]
    		theta = var[2*N:3*N]
    		thetadot = var[3*N:4*N]
    		a = var[4*N:5*N]
    		dynvars = (x,v,theta,thetadot)
    		xavg, vavg, thetavg, thdotavg = map(lambda z: (z[0:-1]+z[1:])/2, dynvars)
    		dx, dv, dthet, dthdot = map(lambda z: (z[1:]-z[0:-1])*dtinv, dynvars)
    		vres = dv - a[1:]
    		xres = dx - vavg
    		torque = (-gL*np.sin(thetavg) + a[1:]*L*np.cos(thetavg))/2
    		thetdotres = dthdot - torque*Iinv
    		thetres = dthet - thdotavg
    
    		return x[0:1]-x0, v[0:1]-v0, theta[0:1]-th0, thetadot[0:1]-thd0, xres,vres, thetdotres, thetres
    		#return x[0:5] - 0.5
    
    
    
    	def getAlu(self, x, x0, v0, th0, thd0):
    		N = self.N
    		gt = np.zeros((2,N))
    		gt[0,:] = -0.1 # 0.15 # x is greaer than 0.15
    		gt[1,:] = -3 #-1 #veclotu is gt -1m/s
    		#gt[4,:] = -10
    		control_n = max(3, int(0.1 / self.dt)) # I dunno. 4 seems to help
    		#print(control_n)
    
    		gt[:,:control_n] = -100
    		#gt[1,:2] = -100
    		#gt[1,:2] = -15
    		#gt[0,:3] = -10
    		gt = gt.flatten()
    		lt = np.zeros((2,N))
    		lt[0,:] = 1 #0.75 # x less than 0.75
    		lt[1,:] = 3 #1 # velocity less than 1m/s
    		#lt[4,:] = 10
    		lt[:,:	control_n] = 100
    		#lt[1,:2] = 100
    		#lt[0,:3] = 10
    		#lt[1,:2] = 15
    		
    		lt = lt.flatten()
    
    		z = sparse.bsr_matrix((N, N))
    		ineqA = sparse.bmat([[sparse.eye(N),z,z,z,z],[z,sparse.eye(N),z,z,z]]) #.tocsc()
    		#print(ineqA.shape)
    		#print(ineqA)
    		cons = self.constraint(forward.seed_sparse_gradient(x), x0, v0, th0, thd0)
    		A = sparse.vstack(map(lambda z: z.dvalue, cons)) #  y.dvalue.tocsc()
    		#print(A.shape)
    		totval = np.concatenate(tuple(map(lambda z: z.value, cons)))
    		temp = A@x - totval
    
    
    		A = sparse.vstack((A,ineqA)).tocsc()
    
    		#print(tuple(map(lambda z: z.value, cons)))
    		#print(temp.shape)
    		#print(lt.shape)
    		#print(gt.shape)
    		u = np.concatenate((temp, lt))
    		l = np.concatenate((temp, gt))
    		return A, l, u
    
    
    
    
    
    





