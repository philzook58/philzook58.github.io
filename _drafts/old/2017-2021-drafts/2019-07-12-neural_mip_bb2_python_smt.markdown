---
author: philzook58
comments: true
date: 2019-07-12 14:05:50+00:00
layout: post
link: https://www.philipzucker.com/?p=2107
published: false
slug: neural mip, bb2, python smt
title: neural mip, bb2, python smt
wordpress_id: 2107
---




[https://eli.thegreenplace.net/2018/unification/](https://eli.thegreenplace.net/2018/unification/)







We could combine the simple SAT solver from that one page with a norvig unification







[https://github.com/aimacode/aima-python/blob/master/logic.py](https://github.com/aimacode/aima-python/blob/master/logic.py)







[https://sahandsaba.com/understanding-sat-by-implementing-a-simple-sat-solver-in-python.html](https://sahandsaba.com/understanding-sat-by-implementing-a-simple-sat-solver-in-python.html)







We could also/instead use cvxpy to answer queries about linear stuff.






    
    <code>import cvxpy as cvx
    import copy
    from heapq import *
    import numpy as np
    import itertools
    counter = itertools.count() 
    
    # you might want to look at boolvar to choose next
    # [(boolvar, uparam, lparam, l_np, u_np)]
    # booldict["name"] = (boolvar, uparam, lparam, l_np, u_np)
    
    # all cutoffs should be made relative. Maybe also list them at the top
    
    class BBTreeNode():
        def __init__(self, vars = set(), prob, bool_vars=set(), u_param = None, l_param = None, bool_l = None, bool_u = None):
            self.vars = vars
            self.constraints = constraints
            self.objective = objective
            self.bool_vars = bool_vars
            self.children = []
            self.u = bool_u #np array
            self.l = bool_l
        #def buildProblem(self):
        #    prob = cvx.Problem(cvx.Minimize(self.objective), self.constraints) #i put Minimize, just so you know that I'm assuming it
        #    return prob
        def buildChild(self, new_u = None, new_l = None):
            BBTreeNode(self.vars, self.prob, self.bool_vars, np_u = new_u, np_l = )
        def solve(self):
            self.u_param.value = self.u_np
            self.l_param.value = self.l_np
            # could also load up x for warmstart
            self.prob.solve()
            # if we want to store anything
            self.x = x.value
            self.res = res
    
        def is_integral(self):
            return all([abs(v.value - 1) <= 1e-3 or abs(v.value - 0) <= 1e-3 for v in self.bool_vars])
        def branch(self):
            children = []
            for b in [0,1]:
                    n1 = copy.deepcopy(self) #yeesh. Not good performance wise, but is simple implementation-wise
                    v = n1.heuristic() #dangerous what if they don't do the same one? I need to do it here though because I need access to copied v.
                    n1.constraints.append( v == b ) # add in the new binary constraint
                    n1.children = []
                    n1.bool_vars.remove(v) #remove binary constraint from bool var set
                    n1.vars.add(v) #and add it into var set for later inspection of answer
                    #self.children.append(n1)   # eventually I might want to keep around the entire search tree. I messed this up though
                    children.append(n1)             
            return children
        def heuristic(self):
            # a basic heuristic of taking the ones it seems pretty sure about
            return min([(min(1 - v.value, v.value) , i, v) for i, v in enumerate(self.bool_vars)])[2]
        def bbsolve(self):
            root = self
            res = root.buildProblem().solve()
            heap = [(res, next(counter), root)]
            bestres = 1e20 # a big arbitrary initial best objective value
            bestnode = root # initialize bestnode to the root
            print(heap)
            nodecount = 0
            while len(heap) > 0: 
                nodecount += 1 # for statistics
                print("Heap Size: ", len(heap))
                lower_bound, _, node = heappop(heap)
                if lower_bound < bestres:
                    prob = node.buildProblem()
                    res = prob.solve()
                    print("Result: ", res)
                    if prob.status not in ["infeasible", "unbounded"]:
                        if res > bestres - 1e-3: #even the relaxed problem sucks. forget about this branch then
                            print("Relaxed Problem Stinks. Killing this branch.")
                            pass
                        elif node.is_integral(): #if a valid solution then this is the new best
                                print("New Best Integral solution.")
                                bestres = res
                                bestnode = node
                        else: #otherwise, we're unsure if this branch holds promise. Maybe it can't actually achieve this lower bound. So branch into it
                            new_nodes = node.branch()
                            for new_node in new_nodes:
                                heappush(heap, (res, next(counter), new_node ) )  # using counter to avoid possible comparisons between nodes. It tie breaks
            print("Nodes searched: ", nodecount)      
            return bestres, bestnode
    
    # a simple knapsack problem. we'll want to minimize the total cost of having each of these items, with different sizes.
    # Use a random problem instance
    N = 100
    prices = -np.random.rand(N)
    sizes = np.random.rand(N)
    print(prices)
    x = cvx.Variable(N)
    constraints = []
    u = cvx.Parameter(N)
    u.value = np.ones(N)
    l = cvx.Parameter(N)
    l.value = np.zeros(N)
    constraints += [x <= u, l <= x] #The relaxation of the binary variable constraint
    constraints += [sizes*x <= 5] # total size of knapsack is 5
    objective = prices * x
    bool_vars = {x[i] for i in range(N)} 
    root = BBTreeNode(constraints = constraints, objective= objective, bool_vars = bool_vars)
    res, sol = root.bbsolve()
    print(sorted(list([(v.name(), v.value) for v in sol.bool_vars] + [(v.name(), v.value) for v in sol.vars] ) ))
    
    # For comparison let's do the same problem using a built in mixed integer solver.
    x = cvx.Variable(N, boolean=True)
    constraints = []
    constraints += [x <= 1, 0 <= x]
    constraints += [sizes*x <= 5]
    objective = prices * x
    prob = cvx.Problem(cvx.Minimize(objective),constraints)
    prob.solve()
    print(x.value)</code>






    
    <code>import cvxpy as cvx
    import torch
    import torch.nn.functional as F
    def traj(x0,v0):
        N = 20
        x = cvx.Variable(N)
        v = cvx.Variable(N)
        u = cvx.Variable(N-1)
    
        dt = 0.1
        c = []
    
        c += [x[0] == x0, v[0] == v0]
        for t in range(N-1):
            c += [x[t+1] == x[t] + dt * v[t]]
            c += [v[t+1] == v[t] + dt * (u[t] - x[t])]
        obj = cvx.Minimize(cvx.abs(x[N-1]))
        prob = cvx.Problem(obj, c)
        prob.solve()
        return x.value, v.value, u.value # may also want dual values?
    samples = 100
    inputs = []
    outputs = []
    #build initial data set
    for s in range(samples):
        x0 = np.random.randn()
        v0 = np.random.randn()
        xs, vs, us = traj(x0,v0)
        inputs.append(np.stack(xs[:-1],vs[:-1]))
        outputs.append(us)
    
    import torch.nn as nn
    import torch.nn.functional as F
    import torch.optim as optim
    
    class Net(nn.Module):
        def __init__(self):
            super(Net, self).__init__()
            self.fc1 = nn.Linear(2, 10)  # 6*6 from image dimension
            self.fc2 = nn.Linear(10, 1)
    
    
        def forward(self, x):
            x = F.relu(self.fc1(x))
            x = self.fc2(x)
            return x
    
    while percenterror > 0.05:
        # train neural network.
        t_inputs = torch.tensor(inputs)
        t_outputs = torch.tensor(inputs)
    
    
        net = Net()
        params = list(net.parameters())
        net.zero_grad()  
        
        # create your optimizer. SGD?!?! WHO DO YOU THINK I AM.
        optimizer = optim.SGD(net.parameters(), lr=0.01)
    
        # in your training loop:
        for j in range(1000):
            optimizer.zero_grad()   # zero the gradient buffers
            output = net(t_inputs)
            criterion = nn.MSELoss() # weight? Weight by how bad the example was?
            loss = criterion(output, target)
            loss.backward()
            optimizer.step()    # Does the update
    
    
        #transfer weights into mip problem. See how well we're doing
    
        for p in params:
            # in a sense we are solving for the initial conditions that do the worst
            x0 = cvx.Variable()
            v0 = cvx.Variable()
    
            #simulate using optimal control.
    
            c += [x[0] == x0, v[0] == v0]
                
    
    
            # simulate using neural control
            x = cvx.Variable(N) # may want to swithc to Variables(N,2) for simplicity
            v = cvx.Variable(N)
            def mynet(x):
                c = []
                x = param['W1'] @ y + param['b1']
                y, c1 = relu(x)
                c += c1
                x = param['W2'] @ y + param['b2']
                return u, c
            for t in range(N-1):
                u, c1 = mynet(x[t])
                c += c1
                c += [xnn[t+1] == xnn[t] + dt * vnn[t]]
                c += [vnn[t+1] == vnn[t] + dt * (u - xnn[t])]
            obj = cvx.Minimize( cvx.abs(x[N-1]) - cvx.abs(xnn[N-1]) ) # This will not be ok. I need to mipify abs? My original version of this use a policy network.
    
    
    
    
    
    
    
           
    
        # Take worst wounterexample, add into training set. iterate`
    
        percenterror = res / 
    w1 = torch.randn(2,10, requires_grad = True)
    b1 = torch.randn(1,10, requires_grad = True)
    w2 = torch.randn(10,1, requires_grad = True)
    b2 = torch.randn(1,1, requires_grad = True)
    y = w1@x + b1
    y = F.relu(y)
    y = w2@y + b2
    y.backward()
    # no this actually does kind of suck.</code>



