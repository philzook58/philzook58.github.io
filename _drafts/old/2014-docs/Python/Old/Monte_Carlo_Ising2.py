import numpy as np
import scipy as sp

beta = 1000
J = .1
Length = 10
steps = 10000

def Energy():
    E = 0
    for i in range(Length):
        E += chain[i]*chain[i-1]
    return -J*E

def Magnetization():
    return np.sum(chain)/Length

def DEnergy(flipspin):
    return 2*J*chain[flipspin]*(chain[flipspin-1]+chain[(flipspin+1)%Length])

def newstate(flipspin):
    chain[flipspin] = -chain[flipspin]

def MonteCarloStep():
    flipspin = np.random.randint(0,Length)  
    dE = DEnergy(flipspin)
    if dE < 0:
        newstate(flipspin)
    else:
        if np.random.random() < np.exp(-beta*dE):
            newstate(flipspin)

chain = (-1)**np.random.randint(1,3,size=Length)
averagemagnet = 0
averageenergy = 0
for i in range(steps):
    MonteCarloStep()
    averagemagnet += Magnetization()/steps
    averageenergy += Energy()/steps

print "Magnetization = " + str(averagemagnet)
print "<Energy> = " + str(averageenergy)

    
    


