import numpy as np
import scipy as sp

beta = 1
J = 1

class Ising:
    chain = []
    length = 0
    def __init__(self,num,initialchain):
        self.chain = initialchain
        self.length = num
            
    def copy(self):
        return Ising(self.length,self.chain)
            
        
    def PerturbState(self):
        new = self.copy()
        change = np.random.randint(0,self.length)
        if new.chain[change] == 0:
            new.chain[change] = 1
        else:
            new.chain[change] = 0
        return new

        
    def DEnergy(self, newstate):
        dE = 0
        for i in range(0,self.length):
            dE += J*(newstate.chain[i]*newstate.chain[i-1]-self.chain[i]*self.chain[i-1])
        return dE  
    

def MonteCarloStep(state):
    newstate = state.PerturbState()
    dE = state.DEnergy(newstate)
    if dE < 0:
        return newstate
    else:
        if np.random.random() > np.exp(-beta*dE):
            return newstate
        else:
            return state
N = 100
model = Ising(N,np.zeros(N))
spinspin = np.zeros(N)
steps = 10000

for i in range(steps):
    model = MonteCarloStep(model)
    for i in range(N):
        spinspin[i] += model.chain[0]*model.chain[i]

spinspin = spinspin/steps
print spinspin
print np.tanh(J*beta)**range(N)

   


    
