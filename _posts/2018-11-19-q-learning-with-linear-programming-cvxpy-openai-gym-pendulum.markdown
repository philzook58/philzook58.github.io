---
author: philzook58
comments: true
date: 2018-11-19 04:46:50+00:00
layout: post
link: https://www.philipzucker.com/q-learning-with-linear-programming-cvxpy-openai-gym-pendulum/
slug: q-learning-with-linear-programming-cvxpy-openai-gym-pendulum
title: Q-Learning with Linear Programming (cvxpy, OpenAI Gym Pendulum)
wordpress_id: 1487
tags:
- optimization
- python
- q-learning
- reinforcement learning
---

[http://web.mit.edu/~pucci/www/discountedLP.pdf](http://web.mit.edu/~pucci/www/discountedLP.pdf)

[http://underactuated.mit.edu/underactuated.html?chapter=dp](http://underactuated.mit.edu/underactuated.html?chapter=dp)

There is a fun idea of using Linear Programming to do dynamic programming I originally saw in the underactuated robotics textbook.

In my experience reinforcement learning is finicky and depressing. It usually doesn't work and is very hard to troubleshoot. Do you just need to run it for 10 minutes? 10 years? Is there a bug? God knows. I end up wriggling hyperparameters and praying a lot.

One part of this is the relative finickiness of neural network optimization compared to the technology of convex optimization. Convex optimization solvers are quite reliable and fast.

There is a way of phrasing Q learning as a linear programming problem

The linear programming approach relaxes the Bellman equations.

$ Q(s_t,a_t)=r_t + \gamma \max_a Q(s_{t+1},a)$

to

$ \forall a. Q(s_t,a_t) \ge r_t +\gamma Q(s_{t+1},a)$

We can approach this forall in a couple ways, one of which is just sampling actions somehow. To make the constraint tight in places you minimize a weighting of Q

$ \min \sum w_i * Q(s_i,a_i) $

If Q is written as a linear combination of basis functions

$ Q(s,a)=\sum \alpha_i f_i(s,a)$

The all of this put together is a linear program in the variables $ \alpha_i$.



For ease, I used cvxpy. I don't even store my state action pairs, which is quite lazy of me. Even here, compiling the linear program via cvxpy is kind of slow. This preprocessing step takes longer than the actual solve does. You could avoid cvxpy and directly interface a linear programming solver much faster, if that is your thing.

The whole process is still model free. I didn't plug in pendulum dynamics anywhere. I run openAI gym and use the resulting state-action-state tuples to add inequalities to my cvxpy model. I weight where I want the inequalities to be tightest by using the actual states experienced.

Unfortunately, it still took a couple hours of hyper parameter tuning and fiddling to get the thing to work. So not a grand success on that point.

I made a lot of guesswork for what seemed reasonable

I parametrized the dependence of Q on `a` by a quadratic so that it is easy to maximize analytically. That is what the polyfit stuff is about. Maximum of $ ax^2+bx+c$ is at $ -b/2a$. I really should be checking the sign of the a coefficient. I am just assuming it is positive. Naughty boy.

m assuming that it

Chebyshev polynomials are probably good.

It seemed to help to use a slight perturbation of the actual action used on the right hand side of the Bellman inequality. My reasoning here is that the pendulum is actually a continuous system, so we should be using the differential Bellman equation really.

Should I allow for some kind of slack in the equations? Getting a bad reward or data point or one weird unusual state could ruin things for everyone. Inequalities are unforgiving.

Gamma seemed to matter a decent amount

The regularization of alpha seemed largely irrelevant.

Epsilon greediness seems to not matter much either.




﻿﻿
Your browser does not support the video tag.




Future ideas:

Might be good to replace the sampling of a with a Sum of Squares condition over the variable a.

Should I damp the update in some way? Add a cost the changing alpha from it's previous value. A kind of damped update / using a prior.



    
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
    
    
    chebdeg = 4
    alpha = cvx.Variable(3*chebdeg**3)
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
        action = -coeff[1]/2/coeff[0]
        action = min(max(action,-2),2)
        return np.array([action])
    
    constraints = []
    objective = 0
    
    
    
    
    for x in range(4):
    
    	constraints = []
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
    	        constraints.append(evalb(alpha, prev_obs, action) >= prev_reward + gamma*evalb(alpha, observation, action + np.random.randn()*0.2))#maxaction(alpha, observation)))
    	        objective += evalb(alpha, observation, env.action_space.sample())
    	        if done:
    	            print("Episode finished after {} timesteps".format(t+1))
    	            break
    	loss = 0.1*cvx.sum(cvx.abs(alpha)) + objective 
    	prob = cvx.Problem(cvx.Minimize(loss), constraints)
    	# The optimal objective value is returned by `prob.solve()`.
    	print("solving problem")
    	result = prob.solve()
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
    








* * *



Edit:

A improved version. Fixed the bug in my maxaction function. I shouldn't have been assuming that it was always concave down.

Also vectorized slightly. Fairly significantly improves the solve time. Not much time is spent in cvxpy, now the solve is dominated by about 3 legitimate seconds in OSQP.

You can flip stuff in and out of loops to try different versions. This method is off-policy, so I could keep data around forever. However, it mostly just slowed the solve time.

    
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
            action = 2
        else:
            action = -2
        return np.array([action])
     
    constraints = []
    objective = 0
     
     
    for x in range(4):
        constraints = []
        objective = 0
     
    
        epsilon = 1.2/(x+1)
        print("epsilon: ", epsilon)
        for i_episode in range(50):
            observation = env.reset()
            observations = []
            rewards = []
            actions = []
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
            constraints += [(bprev@alpha) >= rewards + gamma*(bnext)@alpha]
    
            bcost = np.array([basis(s,env.action_space.sample()).flatten() for s in observations])
            objective += cvx.sum(bcost@alpha) # np.sum(bnext,axis=0) * alpha
        loss = 0.1*cvx.sum(cvx.abs(alpha-alpha.value)) + objective 
        prob = cvx.Problem(cvx.Minimize(loss), constraints)
    
        print("solving problem")
        result = prob.solve(verbose=True)
        print(result)
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
    



