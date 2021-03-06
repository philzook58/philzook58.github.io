---
author: philzook58
comments: true
date: 2018-06-22 14:20:57+00:00
layout: post
link: https://www.philipzucker.com/pytorch-trajectory-optimization/
slug: pytorch-trajectory-optimization
title: Pytorch Trajectory Optimization
wordpress_id: 1110
---

Trajectory optimization is cool. The idea is to take a dynamical problem as a big ole optimization problem, finding the best actions to take to achieve your goals or maximize a reward.

There are a couple of flavors of trajectory optimization (shooting methods, collocation methods) http://www.matthewpeterkelly.com/tutorials/trajectoryOptimization/

PyTorch gives a pretty low overhead extension to Numpy that also gives autodifferentiation. It is mainly intended as a neural network library, for which it has a number of facilities.

Gradient Descent is not the preferred method for these problems (According to Boyd's Convex optimization course). Gradient Descent has shit convergence compared to newton iteration, but is very flexible and easy to implement.

In addition, using a normal ODE solver from Scipy would be much more stable, but it would require cleverness to have the same code work for both scipy and the torch parts. So screw it.

One nicety of this approach is that we don't even have to have our derivatives solved for. They could be all tied up in a

I thought that maybe I could just weight the dynamics cost enough to have it require the dynamics be satisfied, but that did not seem to work. Maybe with more fiddling? On further review my code had massive bugs in it. I'm not sure that the dynamics cost version wouldn't work, but the Lagrange multiplier method seems to work well and makes sense too.

In this formulation, we can also train some kind of parametrized controller function $ f_w(x)$ by sampling some random initial starting conditions (or even dynamical parameters like mass and length etc, or noise forces). This is quite nice.

Additional bits that may be nice: Backtracking line search, logarithmic potential for inequalities, I wonder if a symplectic style interleaving of position and momentum might be nice even for this global case. Should definitely just tie up all the vars into a single x. Can we use a lagrangian or hamiltonian and then have pytorch differentiate that? It may in fact be nice to use some combinator to be able to hand the same function to ODEInt for a couple reasons (getting good initilizations  of the path for example).

For a simple system, I'm using $ \dot{x}=v$ , $ \dot{v}=f$ , where you get to control f at every time point and x is starting at 0 and wants to get to 1. I'm using a simple scheme of finite difference in time for the time derivative. x and v are defined at $ t$ and $ f, lx, lv $ are defined at the half time steps $ t + \frac{1}{2}$. You need at least two time steps to get a derivative. I'm adding a square cost to the force, otherwise it would just get a huge force. lx and lv are Lagrange multipliers enforcing the equations of motion at each time step

Here was an initial pass (just here for for historical reasons, look at the updated one below. This one does not work as is)



    
    import torch
    
    batch = 1
    N = 10
    T = 5
    dt = T/N
    
    x = torch.zeros(batch,N, requires_grad=True)
    
    #print(x)
    
    v = torch.zeros(batch, N, requires_grad=True)
    
    f = torch.zeros(batch, N-1, requires_grad=True)
    
    
    def calc_loss(x,v,f):
    
    	delx = (x[:,1:] - x[:, :-1]) / dt
    	delv = (v[:,1:] - v[:, :-1]) / dt
    
    	xbar = (x[:,1:] + x[:, :-1]) / 2
    	vbar = (v[:,1:] + v[:, :-1]) / 2
    
    	dxdt = vbar
    	dvdt = f
    
    
    	xres = xbar - dxdt
    	vres = vbar - dvdt
    
    	dyn_err = torch.sum(torch.abs(xres) + torch.abs(vres), dim=1) #torch.sum(xres**2 + vres**2, dim=1) # + Abs of same thing?
    
    
    	reward = torch.sum((xbar-1)**2 + f**2, dim=1)
    
    
    	total_cost = 100 * dyn_err + reward
    
    	return total_cost
    
    #print(x.grad)
    #print(v.grad)
    #print(f.grad)
    
    import torch.optim as optim
    '''
    # create your optimizer
    optimizer = optim.SGD(net.parameters(), lr=0.01)
    
    # in your training loop:
    optimizer.zero_grad()   # zero the gradient buffers
    output = net(input)
    loss = criterion(output, target)
    loss.backward()
    optimizer.step()    # Does the update
    '''
    
    #Could interleave an ODE solve step - stinks that I have to write dyanmics twice
    #Or interleave a sepearate dynamic solving
    # Or could use an adaptive line search. Backtracking
    # Goal is to get dyn_err quite small
    
    
    
    learning_rate = 0.001
    for i in range(40):
    	total_cost=calc_loss(x,v,f)
    	#total_cost.zero_grad()
    	total_cost.backward()
    	while dyn_loss > 0.01:
    		dyn_loss.backward()
    		with torch.no_grad():
    			learning_rate = dyn_loss / (torch.norm(x.grad[:,1:]) + (torch.norm(v.grad[:,1:])
    			x[:,1:] -= learning_rate * x.grad[:,1:] # Do not change Starting conditions
    			v[:,1:] -= learning_rate * v.grad[:,1:]
    	reward.backward()
    	with torch.no_grad():
    		f -= learning_rate * f.grad
    
    print(x)
    print(v)
    print(f)


goofed up a couple things (inlcuding my xres making no sense. You need to explicility zero gradients. Pretty annoying). Lagrange multiplier method makes total sense.

Could we use a Hamiltonian and use autograd to derive equations of motion? Seems plausible and convenient.

Can I make a custom pytorch layer for sparse Hessians? The data oriented viewpoint would have you pump the gradient and hessian backward. Or could you automatically build an H-matrix structure for the hessian of convnets?

Put a neural controller in there. Each batch could have randomized parameters, noise, and initial conditions.

Is rebuilding total_cost every time bad?

    
    import torch
    
    batch = 1
    N = 20
    T = 5
    dt = T/N
    
    x = torch.zeros(batch,N, requires_grad=True)
    
    #print(x)
    
    v = torch.zeros(batch, N, requires_grad=True)
    
    f = torch.zeros(batch, N-1, requires_grad=True)
    
    lx = torch.zeros(batch, N-1, requires_grad=True)
    
    lv = torch.zeros(batch, N-1, requires_grad=True)
    
    '''
    class Vars():
    	def __init__(self, N=10):
    		self.data = torch.zeros(batch, N, 2)
    		self.data1 = torch.zeros(batch, N-1, 3)
    		self.lx = self.data1[:,:,0]
    		self.lv = self.data1[:,:,1]
    		self.f = self.data1[:,:,2]
    		self.x = self.data[:,:,0]
    		self.v = self.data[:,:,1]
    '''
    def calc_loss(x,v,f, lx, lv):
            #finite difference derivative
    	delx = (x[:,1:] - x[:, :-1]) / dt
    	delv = (v[:,1:] - v[:, :-1]) / dt
            #average at half time step
    	xbar = (x[:,1:] + x[:, :-1]) / 2
    	vbar = (v[:,1:] + v[:, :-1]) / 2
    
    	dxdt = vbar
    	dvdt = f - xbar
    
            #residual of dynamics (want these numbers to be zeor)
    	xres = delx - dxdt
    	vres = delv - dvdt
    
    	#dyn_err = torch.sum(torch.abs(xres) + torch.abs(vres), dim=1) #torch.sum(xres**2 + vres**2, dim=1) # + Abs of same thing?
    
    	lagrange_mult = torch.sum(lx * xres + lv * vres, dim=1)
    
    
    	cost = torch.sum( torch.abs(x-1), dim=1) + torch.sum( f**2, dim=1) #+ 
    	#cost = torch.sum((x-1)**2, dim=1)
    
    
    	total_cost =   cost + lagrange_mult  #100 * dyn_err + reward
    
    	return total_cost
    
    #print(x.grad)
    #print(v.grad)
    #print(f.grad)
    
    import torch.optim as optim
    '''
    # create your optimizer
    optimizer = optim.SGD(net.parameters(), lr=0.01)
    
    # in your training loop:
    optimizer.zero_grad()   # zero the gradient buffers
    output = net(input)
    loss = criterion(output, target)
    loss.backward()
    optimizer.step()    # Does the update
    '''
    
    #Could interleave an ODE solve step - stinks that I have to write dyanmics twice
    #Or interleave a sepearate dynamic solving
    # Or could use an adaptive line search. Backtracking
    # Goal is to get dyn_err quite small
    
    
    '''
    learning_rate = 0.001
    for i in range(40):
    	total_cost=calc_loss(x,v,f)
    	#total_cost.zero_grad()
    	total_cost.backward()
    	while dyn_loss > 0.01:
    		dyn_loss.backward()
    		with torch.no_grad():
    			learning_rate = dyn_loss / (torch.norm(x.grad[:,1:]) + (torch.norm(v.grad[:,1:])
    			x[:,1:] -= learning_rate * x.grad[:,1:] # Do not change Starting conditions
    			v[:,1:] -= learning_rate * v.grad[:,1:]
    	reward.backward()
    	with torch.no_grad():
    		f -= learning_rate * f.grad
    '''
    learning_rate = 0.001
    for i in range(10000):
    	total_cost = calc_loss(x,v,f, lx, lv)
    	print(total_cost)
    	#print(x)
    	#total_cost.zero_grad()
    
    	total_cost.backward()
    	with torch.no_grad():
    		#print(f.grad)
    		#print(lx.grad)
    		#print(x.grad)
    		#print(v.grad)
    		f -= learning_rate * f.grad
    		lx += learning_rate * lx.grad
    		lv += learning_rate * lv.grad
    		#print(x.grad[:,1:])
    		x[:,1:] -= learning_rate * x.grad[:,1:] # Do not change Starting conditions
    		v[:,1:] -= learning_rate * v.grad[:,1:]
    	x.grad.data.zero_()
    	v.grad.data.zero_()
    	f.grad.data.zero_()
    	lx.grad.data.zero_()
    	lv.grad.data.zero_()
    
    print(x)
    print(v)
    print(f)





