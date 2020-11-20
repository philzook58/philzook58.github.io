---
author: philzook58
comments: true
date: 2018-11-23 04:34:25+00:00
layout: post
link: https://www.philipzucker.com/more-reinforcement-learning-with-cvxpy/
slug: more-reinforcement-learning-with-cvxpy
title: More Reinforcement Learning with cvxpy
wordpress_id: 1509
tags:
- cvxpy
- openai
- python
- reinforcement learning
---

So I spent thanksgiving doing this and playing Zelda. Even though that sounds like a hell of a day, seems a little sad for thanksgiving :(. I should probably make more of an effort to go home next year.

I tried implementing a more traditional q-learning pipeline using cvxpy (rather than the inequality trick of the last time). Couldn't get it to work as well. And it's still kind of slow despite a lot of rearrangement to vectorize operations (through batching basically).

I guess I'm still entranced with the idea of avoiding neural networks. In a sense, that is the old boring way of doing things. The Deep RL is the new stuff. Using ordinary function approximators is way older I think. But I feel like it takes a problem out of the equation (dealing with training neural nets). Also I like modeling languages/libraries.

I kept finding show stopping bugs throughout the day (incorrectly written maxaction functions, typos, cross episode data points, etc.), so I wouldn't be surprised if there is one still in here. It's very surprising how one can convince oneself that it is kind of working when it is actually impossible it's working. All these environments are so simple, that I suspect I could randomly sample controllers out of a sack for the time I've been fiddling with this stuff and find a good one.

    
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
    
    
     
    chebdeg = 2
    alpha = cvx.Variable(3*chebdeg**3)
    alpha.value = np.zeros(3*chebdeg**3)
    gamma = 1. - 1./50
    def basis(s,a):
        n = np.arange(4)
        f1 = chebval(s[0]/1.,np.eye(chebdeg)).reshape(-1,1,1,1)
        f2 = chebval(s[1]/1.,np.eye(chebdeg)).reshape(1,-1,1,1)
        f3 = chebval(s[2]/8.,np.eye(chebdeg)).reshape(1,1,-1,1)
        f4 = ((a/2)**np.arange(3)).reshape(1,1,1,-1)
        return f1*f2*f3*f4
    def vbasis(s,a):
        #n = np.arange(4)
        N = s.shape[0]
    
        #print(chebval(s[:,0]/1.,np.eye(chebdeg)).shape)
        f1 = chebval(s[:,0]/1.,np.eye(chebdeg)).T.reshape(N,-1,1,1,1)
        f2 = chebval(s[:,1]/1.,np.eye(chebdeg)).T.reshape(N,1,-1,1,1)
        f3 = chebval(s[:,2]/8.,np.eye(chebdeg)).T.reshape(N,1,1,-1,1)
        if type(a) == np.ndarray:
            f4 = (a.reshape(-1,1,1,1,1)/2)**(np.arange(3).reshape(1,1,1,1,-1))
        else:
            f4 = (a/2)**(np.arange(3).reshape(1,1,1,1,-1))
        return (f1*f2*f3*f4).reshape(N,-1)
    
    def qmaxaction(alpha,s):
        #n = np.arange(4)
        N = s.shape[0]
    
        #print(chebval(s[:,0]/1.,np.eye(chebdeg)).shape)
        f1 = chebval(s[:,0]/1.,np.eye(chebdeg)).T.reshape(N,-1,1,1,1)
        f2 = chebval(s[:,1]/1.,np.eye(chebdeg)).T.reshape(N,1,-1,1,1)
        f3 = chebval(s[:,2]/8.,np.eye(chebdeg)).T.reshape(N,1,1,-1,1)
        z = f1*f2*f3
        a = (np.array([0,0,0.25]).reshape(1,1,1,1,-1)*z).reshape(N,-1)@alpha.value
        b = (np.array([0,0.5,0]).reshape(1,1,1,1,-1)*z).reshape(N,-1)@alpha.value
    
        acts = np.clip(-b/2/(a+1e-7), -2,2)
        q2 = vbasis(s,2)@alpha.value
        print(acts)
        qa = vbasis(s,acts)@alpha.value
        qn2 = vbasis(s,-2)@alpha.value
        return np.maximum(qa,np.maximum(qn2,q2))
     
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
        epobs = []
        eprewards = []
        epactions = []
        objective = 0
        epsilon = 1.2/(x+1)
        print("epsilon: ", epsilon)
        epNum = 50
        for i_episode in range(epNum):
            observations = []
            rewards = []
            actions = []
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
            epobs.append(observations)
            epactions.append(actions)
            eprewards.append(rewards)
        for qiter in range(20):
            print("Q iteration: ", qiter)
            objective = 0
            for (observations,actions, rewards) in zip(epobs,epactions,eprewards):
                obs = np.array(observations)
                act = np.array(actions)
                bprev = vbasis(obs[:-1],act[1:]) #   np.array([basis(s,a).flatten() for (s,a) in zip(observations[:-1],actions[1:])])
                #bnext = np.array([basis(s,a+np.random.randn()*0.2).flatten() for (s,a) in zip(observations[1:],actions[1:])])
                #obs = np.array(observations)[:-1]
                #q2 = np.array([basis(s,2).flatten() for s in observations[:-1]])@alpha.value
                #q2 = vbasis(obs[1:],2)@alpha.value
                #q0 = vbasis(obs[1:],0)@alpha.value
                #qn2 = vbasis(obs[1:],-2)@alpha.value
                #q1 = vbasis(obs[1:],1)@alpha.value
                #qn1 = vbasis(obs[1:],-1)@alpha.value
                #qs = []
                #for a in np.linspace(-2,2,5):
                #    qs.append(vbasis(obs[1:],a+np.random.randn()*0.5)@alpha.value)
                #for a in np.linspace(-0.1,0.1,3):
                #    qs.append(vbasis(obs[1:],a)@alpha.value)
    
                #qmax = np.max(np.stack([q2,q0,qn2,q1,qn1],axis=1),axis=1)
                #qmax = np.max(np.stack(qs,axis=1),axis=1)
                qmax = qmaxaction(alpha, obs[1:])
    
    
                #q0 = np.array([basis(s,0).flatten() for s in observations[:-1]])@alpha.value
                #qn2 = np.array([basis(s,-2).flatten() for s in observations[:-1]])@alpha.value
               
                #qmax = np.maximum(np.maximum(q0,q2),qn2)#np.array([np.dot(basis(s, maxaction(alpha,s)).flatten(),alpha.value) for s in observations[1:]])
                rewards = np.array(rewards)[:-1]
                objective += cvx.sum(cvx.huber(bprev@alpha - (rewards + gamma*qmax))) #cvx.sum_squares(bprev@alpha - (rewards + gamma*qmax))
    
            #bcost = np.array([basis(s,env.action_space.sample()).flatten() for s in observations])
            #objective = cvx.sum(bcost@alpha) # np.sum(bnext,axis=0) * alpha
            loss = 0.001*cvx.sum_squares(alpha-alpha.value) + objective 
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
    




I also did the easy cartpole environment using the inequality trick.  Seems to work pretty well.

    
    import gym
    import numpy as np
    import cvxpy as cvx
    from numpy.polynomial.chebyshev import chebval
    env = gym.make('CartPole-v1')
    print(env.action_space)
     
    print(env.observation_space)
    print(env.observation_space.high)
     
    print(env.observation_space.low) # [1,1,8]
    #print(env.action_space.high) # -2
    #print(env.action_space.low)
     
     
    chebdeg = 3
    alpha = cvx.Variable(2*chebdeg**4)
    alpha.value = np.zeros(2*chebdeg**4)
    gamma = 1. - 1./25
    def basis(s,a):
        n = np.arange(4)
        f1 = chebval(s[0]/4.,np.eye(chebdeg)).reshape(-1,1,1,1,1)
        f2 = chebval(s[1]/10.,np.eye(chebdeg)).reshape(1,-1,1,1,1)
        f3 = chebval(s[2]/0.4,np.eye(chebdeg)).reshape(1,1,-1,1,1)
        f4 = chebval(s[3]/10.,np.eye(chebdeg)).reshape(1,1,1,-1,1)
        f5 = ((a/2)**np.arange(2)).reshape(1,1,1,1,-1)
        return f1*f2*f3*f4*f5
     
    def evalb(alpha, s,a):
        f = basis(s,a)
        return alpha*f.flatten()
     
    def maxaction(alpha, obs):
        f1 = np.sum(evalb(alpha.value, observation, 0))
        f2 = np.sum(evalb(alpha.value, observation, 1))
        if f1 > f2:
            action = 0
        else:
            action = 1
        return action
     
    constraints = []
    objective = 0
     
     
    for x in range(4):
        constraints = []
        objective = 0
     
    
        epsilon = 1.2/(x+1)
        print("epsilon: ", epsilon)
        for i_episode in range(200):
            observation = env.reset()
            observations = []
            rewards = []
            actions = []
            reward = -100
            for t in range(50):
     
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
            #print(rewards)
            bprev = np.array([basis(s,a).flatten() for (s,a) in zip(observations[:-1],actions[1:])])
            bnext = np.array([basis(s,env.action_space.sample()).flatten() for (s,a) in zip(observations[1:],actions[1:])])
            rewards = np.array(rewards)[:-1]
            constraints += [(bprev@alpha) >= rewards + gamma*(bnext)@alpha]
    
            bcost = np.array([basis(s,env.action_space.sample()).flatten() for s in observations])
            objective += cvx.sum(bcost@alpha) # np.sum(bnext,axis=0) * alpha
        loss = 1*cvx.sum(cvx.abs(alpha-alpha.value)) + objective 
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
    






I also have some Work in Progress on getting full swingup cartpole. Currently is not really working. Seems to kind of be pumping about right? The continuous force control easy cartpole does work though.

    
    import gym
    import numpy as np
    import cvxpy as cvx
    from numpy.polynomial.chebyshev import chebval
    env = gym.make('CartPole-v1')
    print(env.action_space)
     
    print(env.observation_space)
    print(env.observation_space.high)
     
    print(env.observation_space.low) # [1,1,8]
    #print(env.action_space.high) # -2
    #print(env.action_space.low)
     
     
    chebdeg = 2
    varNum = 2*2*4*2*2*3
    alpha = cvx.Variable(varNum)
    alpha.value = np.zeros(varNum)
    gamma = 1. - 1./150
    def basis(s,a):
        n = np.arange(4)
        f1 = chebval(s[0]/4.,np.eye(2) ).reshape(-1,1,1,1,1,1)
        f2 = chebval(s[1]/10.,np.eye(2)).reshape(1,-1,1,1,1,1)
        f3 = chebval(s[2]/1,np.eye(4)  ).reshape(1,1,-1,1,1,1)
        f4 = chebval(s[3]/1,np.eye(2)  ).reshape(1,1,1,-1,1,1)
        f5 = chebval(s[4]/10.,np.eye(2)).reshape(1,1,1,1,-1,1)
        f6 = ((a/10)**np.arange(3)).reshape(1,1,1,1,1,-1)
        return f1*f2*f3*f4*f5*f6
     
    def evalb(alpha, s,a):
        f = basis(s,a)
        return alpha*f.flatten()
    '''
    def maxaction(alpha, obs):
        f1 = np.sum(evalb(alpha.value, observation, 0))
        f2 = np.sum(evalb(alpha.value, observation, 1))
        if f1 > f2:
            action = 0
        else:
            action = 1
        return action
    '''
    def maxaction(alpha, obs):
        f1 = np.sum(evalb(alpha.value, observation, 10))
        f2 = np.sum(evalb(alpha.value, observation, 0))
        f3 = np.sum(evalb(alpha.value, observation, -10))
        coeff = np.polyfit([10,0,-10], [f1,f2,f3], deg=2)
        if coeff[0] < 0:
            action = -coeff[1]/2/coeff[0]
            action = min(max(action,-10),10)
        elif f1 > f3:
            action = 10
        else:
            action = -10
        return np.array([action])
    
    constraints = []
    objective = 0
     
     
    for x in range(4):
        constraints = []
        objective = 0
     
    
        epsilon = 1.2/(x+1)
        print("epsilon: ", epsilon)
        for i_episode in range(100):
            observation = env.reset()
            observations = []
            rewards = []
            actions = []
            reward = -100
            env.env.state[2] = np.random.rand()*2*np.pi
            for t in range(100):
     
                prev_obs = observation
                prev_reward = reward
                if np.random.rand() < epsilon or len(observation) < 5:
                    action = np.random.rand()*20-10
                else:
                    action = maxaction(alpha, observation)
                a = action
                env.env.force_mag = abs(a) #min(100, abs(a))
                #print(a)
                if a < 0:
                    daction = 0
                else:
                    daction = 1
                observation, reward, done, info = env.step(daction)
                o = observation
                observation = np.array([o[0],o[1],np.cos(o[2]),np.sin(o[2]),o[3]])
    
                observations.append(observation)
                bonus = 0
                if observation[2] > 0.9:
                    bonus = 1
    
                rewards.append( (bonus + observation[2] + 1)/2)#- observation[0]**2) #reward
                #print(rewards[-1])
                actions.append(action)
    
                #constraints.append(evalb(alpha, prev_obs, action) >= prev_reward + gamma*evalb(alpha, observation, action + np.random.randn()*0.2))#maxaction(alpha, observation)))
                #objective += evalb(alpha, observation, env.action_space.sample())
                x = observation[0]
                if x < -4 or x > 4:
                    break
                #if done:
                #    print("Episode finished after {} timesteps".format(t+1))
                #    break
            #print(rewards)
            bprev = np.array([basis(s,a).flatten() for (s,a) in zip(observations[:-1],actions[1:])])
            bnext = np.array([basis(s,a+np.random.randn()*0.3).flatten() for (s,a) in zip(observations[1:],actions[1:])])
            rewards = np.array(rewards)[:-1]
            #print(bprev.shape)
            #print(bnext.shape)
    
            constraints += [(bprev@alpha) >= rewards + gamma*(bnext)@alpha]
    
            bcost = np.array([basis(s,a+np.random.randn()*0.3).flatten() for s in observations])
            objective += cvx.sum(bcost@alpha) # np.sum(bnext,axis=0) * alpha
        loss = 1*cvx.sum(cvx.abs(alpha-alpha.value)) + objective 
        prob = cvx.Problem(cvx.Minimize(loss), constraints)
    
        print("solving problem")
        result = prob.solve(verbose=True)
        print(result)
        print(alpha.value)
        #inspection loop
        for i_episode in range(4):
            observation = env.reset()
            env.env.state[2] = np.random.rand()*2*np.pi
            #env.env.state[0] = np.random.randn()*sigma 
            o = observation
            observation = np.array([o[0],o[1],np.cos(o[2]),np.sin(o[2]),o[3]])
            for t in range(200):
                env.render()
                #print(observation)
                prev_obs = observation
                o = observation
                observation = np.array([o[0],o[1],np.cos(o[2]),np.sin(o[2]),o[3]])
                action = maxaction(alpha, observation)
                a = action
                env.env.force_mag = abs(a) #min(100, abs(a))
                #print(a)
                if a < 0:
                    daction = 0
                else:
                    daction = 1
                print(action)
     
                observation, reward, done, info = env.step(daction)
    
                if x < -4 or x > 4:
                    break
    




Now I feel that a thing that matters quite a bit is what is your choice of action for the next time step. Hypothetically you want a ton of samples here. I now think that using an action that is just slightly perturbed from the actual action works well because the actual action is tending to become roughly the optimal one. Subsequent time steps have roughly the same data in them.

One advantage of discrete action space is that you can really search it all.

Does that mean I should seriously investigate the sum of squares form? A semidefinite variable per data point sounds bad. I feel like I'd have to seriously limit the amount of data I'm using. Maybe I'll be pleasantly surprised.

I haven't even gotten to playing with different polynomials yet. The current implementation is exponentially sized in the number of variables. But in kind of a silly way. I think it would be better to use all terms of a bounded total degree.


