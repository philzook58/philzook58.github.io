import numpy as np
import scipy as sp
import matplotlib.pyplot as plt

#Wave equation solver - Philip Zucker 2011

def Gaussian(x,b,sigma):
    return np.exp(-((x-b)/sigma)**2)

size = 500
L = 1. #Total x length
dx = L/size

timestep = 1500
Time = 1.
dt = Time/timestep
c = 1 #c, speed of wave
c2 = c**2
K = np.tri(size,k=1)-np.tri(size,k=-2)-3*np.identity(size)
K = K/dx**2*c2*dt**2 + 2*np.identity(size)

#Boundary Conditions
K[0,0]=1
K[0,1]=0
K[1,0]=0

K[size-1,size-1]=1
K[size-1,size-2]=0
K[size-2,size-1]=0
        
print K
x= np.linspace(0,L,size)
y = np.zeros((timestep,size))

"""
#Moving Gaussian function
y[0,:] = Gaussian(x,L/2,10*dx)
y[1,:]=Gaussian(x,L/2 + c*dt,10*dx)
"""

#Initially Unmoving Gaussian
"""
y[0,:] = Gaussian(x,L/2,10*dx)


y[1,:]=Gaussian(x,L/2,10*dx)
"""

#Initially Unmoving delta function
"""
y[0,size/2]=1
y[1,size/2]=1
"""
"""
#Appearing Delta
y[0,size/2]=0
y[1,size/2]=1
"""

#Appearing gaussian
y[1,:]=Gaussian(x,L/2,10*dx)


"""
#Oscillating sine wave with given nodes
mode = 7
y[0,:]=np.sin(mode*sp.pi*x/L)
y[1,:]=.999999*y[0,:]
"""

#Solver
for i in range(2,timestep):
    y[i,:]=np.dot(K,y[i-1,:])-y[i-2,:]
    

#plottimes(20)
leg = []
for i in range(0,7):
        plt.plot(x,y[i/8.*timestep,:])
        leg.append('t = ' + str(i))

plt.legend(leg)
plt.show()



