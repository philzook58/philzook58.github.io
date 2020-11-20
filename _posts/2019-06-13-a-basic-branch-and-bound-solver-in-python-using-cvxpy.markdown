---
author: philzook58
comments: true
date: 2019-06-13 20:29:54+00:00
layout: post
link: https://www.philipzucker.com/a-basic-branch-and-bound-solver-in-python-using-cvxpy/
slug: a-basic-branch-and-bound-solver-in-python-using-cvxpy
title: A Basic Branch and Bound Solver in Python using Cvxpy
wordpress_id: 2084
categories:
- Optimization
tags:
- python
---




[Branch and bound](https://en.wikipedia.org/wiki/Branch_and_bound) is a useful problem solving technique. The idea is, if you have a minimization problem you want to solve, maybe there is a way to relax the constraints to an easier problem. If so, the solution of the easier problem is a lower bound on the possible solution of the hard problem. If the solution of the easier problem just so happens to also obey the more constrained hard problem, then it must also be the solution to the hard problem. You can also use the lower bound coming from a relaxed problem  to prune your search tree for the hard problem. If even the relaxed problem doesn't beat the current best found, don't bother going down that branch.







A standard place this paradigm occurs is in mixed integer programming. The relaxation of a binary constraint (either 0 or 1) can be all the values in between (any number between 0 and 1). If this relaxed problem can be expressed in a form amenable to a solver like a linear programming solver, you can use that to power the branch and bound search, also using returned solutions for possible heuristics.







I built a basic version of this that uses[ cvxpy](https://www.cvxpy.org/) as the relaxed problem solver. Cvxpy already has much much faster mixed integer solvers baked in (which is useful to make sure mine is returning correct results), but it was an interesting exercise. The real reason I'm toying around is I kind of want the ability to add custom branching heuristics or inspect and maintain the branch and bound search tree, which you'd need to get into the more complicated guts of the solvers bound to cvxpy to get at. [Julia](https://julialang.org/) might be a better choice.







A somewhat similar (and better) project is [https://github.com/oxfordcontrol/miosqp](https://github.com/oxfordcontrol/miosqp) which doesn't use cvxpy explicitly, but does have the branch and bound control in the python layer of the solver. There are also other projects that can use fairly arbitrary solvers like [Bonmin](https://projects.coin-or.org/Bonmin)







As a toy problem I'm using a knapsack problem where we have objects of different sizes and different values. We want to maximize the value while keeping the total size under the capacity of the bag. This can be phrased linearly like so: $latex \max v \cdot x$ s.t. $latex \sum_i s_i x_i<= capacity $, $latex x \in {0,1}$. The basic heuristic I'm using is to branch on variables that are either 0 or 1 in even the relaxed solution. The alternative branch hopefully gets pruned fast.






    
    <code>import cvxpy as cvx
    import copy
    from heapq import *
    import numpy as np
    import itertools
    counter = itertools.count() 
    
    class BBTreeNode():
        def __init__(self, vars = set(), constraints = [], objective=0, bool_vars=set()):
            self.vars = vars
            self.constraints = constraints
            self.objective = objective
            self.bool_vars = bool_vars
            self.children = []
        def buildProblem(self):
            prob = cvx.Problem(cvx.Minimize(self.objective), self.constraints) #i put Minimize, just so you know that I'm assuming it
            return prob
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
                _, _, node = heappop(heap)
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
    N = 20
    prices = -np.random.rand(N)
    sizes = np.random.rand(N)
    print(prices)
    x = cvx.Variable(N)
    constraints = []
    constraints += [x <= 1, 0 <= x] #The relaxation of the binary variable constraint
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







This is at least solving the problem fairly quickly. It needs better heuristics and to be sped up, which is possible in lots of ways. I was not trying to avoid all performance optimizations. It takes maybe 5 seconds, whereas the cvxpy solver is almost instantaneous. 






    
    <code>Nodes searched:  67
    [('var0[0]', 0.9999999958228145), ('var0[10]', -1.2718338055950193e-08), ('var0[11]', -1.3726395012104872e-08), ('var0[12]', 0.9999999982326986), ('var0[13]', 0.9999999973744331), ('var0[14]', 0.9999999988156902), ('var0[15]', -1.1908085711772973e-08), ('var0[16]', 0.9999999903780872), ('var0[17]', 0.9999999863334883), ('var0[18]', -1.1481655920777931e-08), ('var0[19]', 0.9999999996667646), ('var0[1]', 0.9999999969549299), ('var0[2]', 0.9999999979596141), ('var0[3]', -9.282428548104736e-09), ('var0[4]', -1.1378022795740783e-08), ('var0[5]', 0.9999999868240312), ('var0[6]', 0.9999999995068807), ('var0[7]', 0.9999999995399617), ('var0[8]', 0.9999999859520627), ('var0[9]', 0.9999999948062767)]
    [ 1.00000000e+00  1.00000000e+00  1.00000000e+00 -1.44435650e-12
     -1.88491321e-12  1.00000000e+00  1.00000000e+00  1.00000000e+00
      1.00000000e+00  1.00000000e+00 -7.11338729e-13  1.99240081e-13
      1.00000000e+00  1.00000000e+00  1.00000000e+00 -1.48697107e-12
      1.00000000e+00  1.00000000e+00 -1.75111698e-12  1.00000000e+00]</code>







Edit : I should investigate the Parameter functionality of cvxpy. That would make a make faster version than the one above based on deepcopy. If you made the upper and lower vectors on the binary variables parameters, you could restrict the interval to 0/1 without rebuilding the problem or copying everything. 






    
    <code>#rough sketch
    b = cvx.Variable(N) 
    u = cvx.Parameter(N) 
    u.value = np.ones(N)
    l = cvx.Parameter(N) 
    l.value = np.zeros(N)
    constraints += [b <= u, l <= b]
    # change l.value and u.value in search loop.</code>









