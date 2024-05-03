---
author: philzook58
comments: true
date: 2019-04-27 18:03:10+00:00
layout: post
link: https://www.philipzucker.com/?p=1921
published: false
slug: Jump graph color
title: Jump graph color
wordpress_id: 1921
---

using JuMP  
using Cbc  
using LightGraphs  
m = Model(solver=CbcSolver(Sec=60))  
colors = 20  
n_nodes = 35  
@variable(m, x[1:n_nodes, 1:colors], Bin)  
@constraint(m, sum(x,dims=2) .>= 1 ) # everyone needs at least one color  
g = SimpleGraph(n_nodes, n_nodes * 10, seed=-1) #n nodes 5 times as many edges  
for edge in edges(g)  
@constraint(m, x[edge.src, :] .<= 1 - x[edge.dst, :]) #suppression both ways. Only one can be on  
@constraint(m, x[edge.dst, :] .<= 1 - x[edge.src, :])  
end




@objective(m, Max, sum(x)) #pack as many colors as possible, simple objective. Weight by layer?solve()




solve(m)  
getvalue(x)  
sum(getvalue(x),dims=2)  
xsol = getvalue(x)  
for edge in edges(g)  
print(reduce(&, xsol[edge.src, :] .<= 1 .- xsol[edge.dst, :])) #suppression both ways. Only one can be on  
print(reduce(&,xsol[edge.dst, :] .<= 1 .- xsol[edge.src, :]))  
end  
getobjectivevalue(m)





    
    <code>using JuMP
    using Cbc
    using LightGraphs
    m = Model(solver=CbcSolver(Sec=60))
    colors = 20
    n_nodes = 35
    @variable(m, x[1:n_nodes, 1:colors], Bin)
    @constraint(m, sum(x,dims=2) .>= 1 ) # everyone needs at least one color
    g = SimpleGraph(n_nodes, n_nodes * 10, seed=-1) #n nodes 5 times as many edges
    for edge in edges(g)
    @constraint(m, x[edge.src, :]  .<= 1 - x[edge.dst, :]) #suppression both ways. Only one can be on
    @constraint(m, x[edge.dst, :]  .<= 1 - x[edge.src, :])
    end
    
    @objective(m, Max, sum(x)) #pack as many colors as possible, simple objective. Weight by layer?solve()
    
    solve(m)
    getvalue(x)
    sum(getvalue(x),dims=2)
    xsol = getvalue(x)
    for edge in edges(g)
    print(reduce(&, xsol[edge.src, :]  .<= 1 .- xsol[edge.dst, :])) #suppression both ways. Only one can be on
       print(reduce(&,xsol[edge.dst, :]  .<= 1 .- xsol[edge.src, :]))
    end
    getobjectivevalue(m)</code>







Weight inner nodes ~10x as much. Use greedy coloring to fix boundary conditions of layer 3 for example. Is this enough symmettry breaking?







Could do sweep of layer n through layer n+3. Initialize everything with greedy. Do cbc optimization of each. Do sweep of single layer at a time?







better representation 







I am a doof. Those two color constraint are both a + b <= 1. They can't both be 1 cause that would 













Initial attempt at randomizing weights didn't help. CBC might already be recognizing symettries?







10% gap?












    
    <code>#sketch of simulations
    t = 0
    hub = graph.hub
    while True:
       t += 1
       for node in graph.nodes():
          timeslot = t % 32
          if node['schedule'][timeslot]:
             for neigh in node.neighbors():
                 if neigh == hub:
                 else:
    
                 angle = np.random.random()*2*np.pi
                 c = np.cos(angle)
                 s = np.sin(angle)
                 neigh.data = c*neigh.data + s * node.data
                 neigh.coeff = c*neigh.coeff + s * node.coeff
    
    
    </code>






    
    <code>#sketch of simulations
    
    # we may want to break into pieces
    numGroups = graph.
    
    def resetHubStore(hub):
        hub['store'] = [{'data': [], 'coeff' : []}] * numGroups # bug waiting to happen? Is that dict gonna be shared?
    
    def hubsolve(hub):
        coeff_mat = np.array(neigh.coeff)
        solved_nodes = numpy.linalg.matrix_rank(coeff_mat)
        return solved_nodes
    
        # alternative, using least squares solve. Also gives singular values and actual data solution. Needs to be regularized?
        data_mat = np.array(neigh.data)
        x, res, rank, sings = numpy.linalg.lstsq(coeff_mat, data_mat)
    
    # do the nodes need to mixin for multiple groups?
    def initNetworkData(activeGroup, graph):
        for node in graph.nodes():
            if node['group'] == activeGroup:
               nodeId = node['nodeId']
               node['data'] =  np.repeat(float(nodeId) , 50) # could reduce 50 down to 3 or 1 even.
               node['coeff'] =  np.zeros(78)
               node['coeff'][nodeId] = 1
            else:
               node['data'] = np.zeros(50)
               node['coeff'] =  np.zeros(78)
               
    
    def mixinMessage(node, data, coeff):
        angle = np.random.random()*2*np.pi
        c = np.cos(angle)
        s = np.sin(angle)
        node.data = c * node.data + s * data
        node.coeff = c * node.coeff + s * coeff
        if node.group = group:
            angle = np.random.random()*2*np.pi
            c = np.cos(angle)
            s = np.sin(angle)
            node.data = c * node.data + s * node.selfdata
            node.coeff = c * node.coeff + s * node.selfcoeff
        norm = np.linalg.norm(node.data) + np.linalg.norm(node.coeff) #considered as one big vector (this normalization may not be necessary)
        node.data /= norm
        node.coeff /= norm
    
    timetable = [[]]*32
    for t in range(32):
       for node in graph.nodes():
            if node['schedule'][timeslot] == True and node != hub:
                timetable[t].append(node)
    resetHubStore(hub)
    
    
    def simulateGroupPoll(groupId, graph, timeout = 100000000):
        #miscelaneous setup
        activeGroup = 1 # groupID
        initNetworkData(activeGroup, graph)
        hub = graph.hub
    
        t = 0
        solvedNodes = []
        groupsize = graph.groupSizes[activeGroup]
    
        # main loop 
        for t in range(timeout):
            timeslot = t % 32
            for node in timetable[timeslot]:
                    for neigh in node.neighbors():
                        if neigh == hub: # hub receives message. Put it into the store.
                            hub['store'][activeGroup]['coeff'].append(np.copy(neigh.coeff))
                            hub['store'][activeGroup]['data].append(np.copy(neigh.data))
                        else:
                            mixinMessage(neigh, node.data, node.coeff)
            solved_nodes = hubsolve(hub, activeGroup)
            solvedNodes.append(solved_nodes)
            if solved_nodes >= groupsize: #is this what we want?
                break
        return solvedNodes
    </code>



