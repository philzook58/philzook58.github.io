---
author: philzook58
comments: true
date: 2018-11-26 21:37:34+00:00
layout: post
link: https://www.philipzucker.com/?p=1514
published: false
slug: 'Bits and Bobbles from Reinforcement Learning:'
title: 'Bits and Bobbles from Reinforcement Learning:'
wordpress_id: 1514
---

Note: Probably a particularly unhelpful post to anyone but me.

I have been having some difficulty. Swing-up cartpole is killing me.

Reinforcement learning truly is machine learning. I have immediately been tempted to try ad hoc bull shit and see what sticks.

I got CBC running as a backend. I had to get CyLP installed which was kind of a pain. Nevertheless, now I am truly using an LP solver. And it is pretty fast.

If one takes the product of all polynomials up to some power d, you get d^N dependence of the total LP variables in terms of N state variables.

If you use all polynomials of total power d you have N^d dependence, which is better usually.

One straightforward way to do this is prebuild a power matrix.

    
    def coeffs(N,d):
        if d == 0:
            return [np.zeros(N)]  
        q = coeffs(N,d-1)
        res = []
        for row in q:
            for i in range(N):
                row1 = np.copy(row)
                row1[i] += 1
                res.append(row1)
        return res
    
    d = 3
    exps = np.array(coeffs(6,d))
    print(exps)
    #chebdeg = 2
    
    varNum = exps.shape[0]*2
    print(varNum)
    alpha = cvx.Variable(varNum)
    alpha.value = np.zeros(varNum)
    gamma = 1. - 1./70
    F = 20
    def basis(s,a):
        global exps
        #print(s.shape)
        x,v,c,s,om = s.flatten()
        s = np.array([1,x/6,v/10,c,s,om/10])
        #s = np.concatenate(([1],s.flatten())).reshape(1,-1)
        f = np.prod(s**exps, axis=1)
        f6 = ((a/F)**np.arange(2)).reshape(1,-1)
        return f.reshape(-1,1)*f6
    
    
    def evalb(alpha, s,a):
        f = basis(s,a)
        return alpha*f.flatten()


A more interesting way might be to build a Dynamic Programming datastructure for computing all these products as there is a lot of sharing of terms. This seemed fast enough for my purposes though. It's all swamped by LP solve time.

LP solvers thrive on sparsity. Switching over to a localized spline representation makes each state-action-reward-state datapoint into a sparse row. This makes the LP solve significantly faster. I'm using a piecewise linear approximation based on simplices of your nearest neighbors. This is not the delauney triangulation? Maybe I should be using that? It's pretty easy to interpolate the values at the points of a simplex using homogenous coordinates / the barycentric coordinates of that simplex.

Nevertheless, I'm still not having much luck.

It is hard to ascertain the problem:

1. Not enough data?

2. Not enough flexibility in the function space? Too much? Bad symmetry? Possibly need to be very careful with parametrization around the balancing point

3. Bad Parameters (gamma, regularization)

4. A poor reward function?

5. The most likely of all, just huge glaring bugs making whatever I'm running total nonsense.



A neural network made of linear and relu layers is a piecewise linear function. Piecewise linear functions are closed under composition. They do not cover ALL piecewise linear functions though. The total number of simplices might be very large. Each row in a linear layer add a new hyperplane, and I think subsequent layers probably multiplies the total number of simplices.

I have tried randomly picking the interpolation points, but it seems reasonable to me that one could use an adaptive scheme, especially if slack in the bellman inequality signifies a lack of flexibility of the function basis in that simplex.

The dual may also contain useful information. Perhaps overfitting info? Or importance of data point info?

Or a single roll of Q-iteration fitting and see where the fit is poor.

We don't actually care about Q function accuracy. We actually want just the correct maximal actions. So the slack divided by the variance among different actions may set a scale

One could add the centroid of that simplex into the point set. Do this iteratively.

Also, one could perhaps sense redundancy by having too well fitting. A tightness in the slack. One could randomly remove a percentage of the points. If that point really did matter, it will get added back in.

Or one could try adding points and see what the Richardson extrapolation error is? Like how much the Q-function changes with increasing resolution. Not sure you can even compute this though.

The use of an isotropic metric is very fishy. At the very least it should be dimensionally scaled.

Given the actual equations of motion, one could conceive of getting an actual error metric, like is done in adaptive meshes for solving PDEs or ODEs.

One could also take derivatives with respect to the current point positions and slightly adjust them using gradient descent.

All seem plausible to me, but also total bull crap without something more formal to motivate them.



    
    import gym
    import numpy as np
    import cvxpy as cvx
    from numpy.polynomial.chebyshev import chebval
    import scipy.sparse as sparse
    env = gym.make('CartPole-v1')
    print(env.action_space)
     
    print(env.observation_space)
    print(env.observation_space.high)
     
    print(env.observation_space.low) # [1,1,8]
    #print(env.action_space.high) # -2
    #print(env.action_space.low)
     
     
    chebdeg = 2
    #varNum = 3*2*3*3*2*2
    #alpha = cvx.Variable(varNum)
    #alpha.value = np.zeros(varNum)
    #gamma = 1. - 1./150
    '''
    def basis(s,a):
        n = np.arange(4)
        f1 = chebval(s[0]/4.,np.eye(3) ).reshape(-1,1,1,1,1,1)
        f2 = chebval(s[1]/10.,np.eye(2)).reshape(1,-1,1,1,1,1)
        f3 = chebval(s[2]/1,np.eye(3)  ).reshape(1,1,-1,1,1,1)
        f4 = chebval(s[3]/1,np.eye(3)  ).reshape(1,1,1,-1,1,1)
        f5 = chebval(s[4]/10.,np.eye(2)).reshape(1,1,1,1,-1,1)
        f6 = ((a/10)**np.arange(2)).reshape(1,1,1,1,1,-1)
        return f1*f2*f3*f4*f5*f6
    '''
    '''
    
    def coeffs(N,d):
        if d == 0:
            return [np.zeros(N)]  
        q = coeffs(N,d-1)
        res = []
        for row in q:
            for i in range(N):
                row1 = np.copy(row)
                row1[i] += 1
                res.append(row1)
        return res
    
    d = 3
    exps = np.array(coeffs(6,d))
    print(exps)
    #chebdeg = 2
    
    varNum = exps.shape[0]*2
    print(varNum)
    
    def basis(s,a):
        global exps
        #print(s.shape)
        x,v,c,s,om = s.flatten()
        s = np.array([1,x/6,v/10,c,s,om/10])
        #s = np.concatenate(([1],s.flatten())).reshape(1,-1)
        f = np.prod(s**exps, axis=1)
        f6 = ((a/F)**np.arange(2)).reshape(1,-1)
        return f.reshape(-1,1)*f6
    
    
    def evalb(alpha, s,a):
        f = basis(s,a)
        return alpha*f.flatten()
    '''
    num_s = 5
    N = 100
    varNum = N*2
    pts = []
    for x in np.linspace(-4,4,3):
        for v in np.linspace(-10,10,3):
            for c in np.linspace(-1,1,3):
                for s in np.linspace(-1,1,4):
                    for om in np.linspace(-10,10,3):
                        pts.append([x,v,c,s,om])
    pts = np.array(pts)
    pts += np.random.randn(*pts.shape)*0.1
    
    '''
    pts = np.random.randn(N,num_s)/2 #np.random.rand(N,num_s)*2 - 1
    pts[:,0] *= 4
    pts[:,1] *= 5
    pts[:,2] *= 1
    pts[:,3] *= 1
    pts[:,4] *= 5
    '''
    '''
    pts = np.zeros((N,num_s))
    pts1 = np.random.randn(N//2,num_s) #np.random.rand(N,num_s)*2 - 1
    pts1[:,0] *= 4
    pts1[:,1] *= 5
    pts1[:,2] *= 1
    pts1[:,3] *= 1
    pts1[:,4] *= 5
    pts[:N//2,:] = pts1
    pts1 = np.random.randn(N//2,num_s) #np.random.rand(N,num_s)*2 - 1
    pts1[:,0] *= 2
    pts1[:,1] *= 4
    pts1[:,2] = 0.4 * pts1[:,2] + 1 
    pts1[:,3] *= 0.4
    pts1[:,4] *= 1
    pts[N//2:,:] = pts1
    '''
    
    
    
    
    alpha = cvx.Variable(pts.shape[0]*2)
    alpha.value = np.zeros(pts.shape[0]*2)
    gamma = 1. - 1./100
    F = 10
    
    
    
    
    def basis(s,a):
        s = s.flatten()
        ds = np.linalg.norm(pts - s.reshape(1,-1), axis=1, ord=1)
        #print(ds.shape)
        inds = np.argsort(ds)
        inds = inds[:num_s+1]
        ds = ds[inds[:num_s+1]]
        neighbs = pts[inds,:]
        #print(neighbs.shape)
        #print(neighbs)
        homo_nei = np.concatenate((neighbs, np.ones((num_s+1,1))), axis = 1)
        homo_s = np.concatenate((s,[1]))
        #print(homo_nei)
        weights = np.linalg.solve(homo_nei.T, homo_s)
        #weights = weights[:-1]/weights[-1]
        #weights = (1./ds) / sum(1./ds) # i totally fucked this up. This makes no sense.
        # at the very least, the closest point should weigh in the most
        if a < 0:
            inds = inds + N #np.concatenate((inds, inds+N))
        #weights = #np.concatenate((weights, weights))
        f = np.zeros(pts.shape[0]*2)
        f[inds] = weights
    
        return f #get simplex
    
    
    # could add smoothing term. Find graph of nearest neighbors nd 
    # add regularization term
    
    # if we add a into the mix to make it conitnunous, it might be an LP to find
    # maximum a given fixed s.
    # maybe it is a MILP. maximizing a piecewise linear function
    # also perhaps only if I used l1 norm for nearest point finding.
    
    
    #adaptive point adding
    #if I fixed the current set of weights? and then take the point postion as an optimization
    # problem. continuous Point adjustment
    # 
    # The dual has interesting information. Anywhere it is loose, we have not enough
    # descriptive power. Anywhere constraints are loose for all actions?
    # maybe with some probability destroy points, add where seems useful
    # maintain the convex hull points though so that our total region doesn't shrink.
    
    # The best possible set of points would be one point per data point.
    # That would just be a table.
    
    # a relu based neural network is a massive piecewise linear function
    # (piecewise linearity is closed under compostion)
    # but it is able to adapt it's piecwsie transition positions.
    #
    
    def evalb(alpha,s,a):
        f = basis(s,a)
        return f * alpha
    
    
    
    
    
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
        f1 = np.sum(evalb(alpha.value, observation, F))
        #f2 = np.sum(evalb(alpha.value, observation, 0))
        f3 = np.sum(evalb(alpha.value, observation, -F))
        #coeff = np.polyfit([10,0,-10], [f1,f2,f3], deg=2)
        #if coeff[0] < 0:
        #    action = -coeff[1]/2/coeff[0]
        #    action = min(max(action,-10),10)
        if f1 > f3:
            action = F
        else:
            action = -F
        return np.array([action])
    
    constraints = []
    objective = 0
    constraints += [alpha <= 500, alpha >= 0]
     
    for x in range(4):
        #constraints = []
        objective = 0 #0.5*objective
     
    
        epsilon = 1.2/(x+1)
        print("epsilon: ", epsilon)
        for i_episode in range(60):
            observation = env.reset()
            o = observation
            observation = np.array([o[0],o[1],np.cos(o[2]),np.sin(o[2]),o[3]])
            observations = []
            rewards = []
            actions = []
            reward = -100
            env.env.state[2] =  np.random.randn()*np.pi/8 #np.random.rand()*np.pi*2
            for t in range(100):
     
                prev_obs = observation
                prev_reward = reward
                if np.random.rand() < epsilon or len(observation) < 5:
                    #np.random.randint(2)
                    action = np.random.randint(2)*2*F-F
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
                x,v,c,s,om = observation 
                if x < -6 or x > 6:
                    break
                if v < -10 or v > 10:
                    break
                if om < -10 or om > 10:
                    break
                observations.append(observation)
                bonus = 0
                #if observation[2] > 0.9:
                    #bonus = 0.5
                #if x < -3 or x > 3:
                    #bonus -= 1
                rewards.append( (bonus + observation[2] + 1) - (observation[0]/3)**2 - (observation[1]/5)**2 - (observation[4]/7)**2 ) #reward
                #print(rewards[-1])
                actions.append(action)
                '''
                constraints.append(evalb(alpha, prev_obs, action) >= prev_reward + gamma*evalb(alpha, observation, F))#maxaction(alpha, observation)))
                constraints.append(evalb(alpha, prev_obs, action) >= prev_reward + gamma*evalb(alpha, observation, -F))#maxaction(alpha, observation)))
                
                objective += evalb(alpha, observation, F)
                objective += evalb(alpha, observation, -F)
                '''
                #x = observation[0]
    
                #if done:
                #    print("Episode finished after {} timesteps".format(t+1))
                #    break
            #print(rewards)
            '''
            J = np.repeat(np.arange(len(observations[:-1]),   (num_s+1)*2)
            bprevV, bprevI = unzip([basis(s,a) for (s,a) in zip(observations[:-1],actions[1:])])
            bprevV = np.array(bprevV).flatten()
            bprevI = np.array(bprevI).flatten()
            bprev = sparse.csc_matrix(bprevV, (brevI,bprevJ))
            '''
            bprev = np.array([basis(s,a).flatten() for (s,a) in zip(observations[:-1],actions[1:])])
           
            bnext = np.array([basis(s,F).flatten() for (s,a) in zip(observations[1:],actions[1:])])
            bnext2 = np.array([basis(s,-F).flatten() for (s,a) in zip(observations[1:],actions[1:])])
            
            rewards = np.array(rewards)[:-1]
            #print(bprev.shape)
            #print(bnext.shape)
    
            constraints += [(bprev@alpha) >= rewards + gamma*(bnext)@alpha]
            constraints += [(bprev@alpha) >= rewards + gamma*(bnext2)@alpha]
    
            #bcost = np.array([basis(s,F).flatten() for (s,a) in zip(observations,actions)])
            #objective += cvx.sum(bcost@alpha) # np.sum(bnext,axis=0) * alpha
            bcost = np.array([basis(s,F).flatten() for s in observations])
            objective += cvx.sum(bcost@alpha) # np.sum(bnext,axis=0) * alpha
            bcost = np.array([basis(s,-F).flatten() for s in observations])
            objective += cvx.sum(bcost@alpha) # np.sum(bnext,axis=0) * alpha
        loss = objective # 1*cvx.sum(cvx.abs(alpha)) +  #-alpha.value
        prob = cvx.Problem(cvx.Minimize(loss), constraints)
    
        print("solving problem")
        result = prob.solve(verbose=True, solver=cvx.CBC)
        print(result)
        print(alpha.value)
        #inspection loop
        for i_episode in range(4):
            observation = env.reset()
            env.env.state[2] = np.random.randn()*np.pi/8  #np.random.rand()*2*np.pi
            #env.env.state[0] = np.random.randn()*sigma 
            o = observation
            observation = np.array([o[0],o[1],np.cos(o[2]),np.sin(o[2]),o[3]])
            for t in range(100):
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
                #print(action)
     
                observation, reward, done, info = env.step(daction)
    
                if x < -4 or x > 4:
                    break
    




Using a grid basis:

If you have your function sampled on a grid, the typical implication is that you are using a piecewise spline.

For a single dimension it is a piecewise linear function, but in higher dimensions, it is a little nonlinear. It is polynomials where any variable appears at most once. In 2d for example $latex a + bx + cy + dxy$ or in 3 dimensions $latex  a + b x + c y + d z + e xy + f yz + g xz + h xyz$. Feels kind of weird, but that is how it is. A cube in d dimensions has 2^d corners. This polynomial has that many terms also.

You can calculate the interpolations by

$latex \sum f_i \prod_j (x_j - \bar{c}_j) / L_i$

where $latex \bar{c}_j$ is the opposite corner of the cube in the j-th dimension. and $latex L_j$ is the length of the cube in the jth dimension. This works because if you plug in any particular corner, all the terms in the sum evaluate to zero except the $latex f_j $ actually coming from that corner. This is Lagrange interpolation.

Very roughly this is the code.

    
    def basis(s,a):
    
       np.array(s[0] - u[0], s[0]-l[1]).reshape(-1,1,1,1,1)/L[0]
    
       np.array(s[0] - u[0], s[0]-l[1]).reshape(-1,1,1,1,1)/L[1]
    
       np.array(s[0] - u[0], s[0]-l[1]).reshape(-1,1,1,1,1)
    
       sparse_zero(full)
    
       z = np.zeros((N0,N1,N2,N3,N4))
    
       z[u[0]:u[0]+2, u[1]:u[1]+2, ] = x*y*z*w*x
    
       return z




I should try using the exact equations of motion.



Linear programming can be solved via the Penalty method. If we apply that reasoning, we can form a single function that avoids needed the maximization over Q like Q learning does. I guess it all feels about the same in the end of the day. sum_a Relu(Q - (r + gamma Q). We no longer need to hold the second part fixed.

Fine-tuning networks. You can use the head layer of the network (the dense section) as the basis for the LP. Then using this as a ground truth Q function, you can iterate (Q - (r + gamma Q)) or you could choose to use the previous method maybe




