import numpy as np
import scipy as sp
import matplotlib.pyplot as plt

#Implicit Heat Equation Solver - Philip Zucker 2011

size = 100 #The x discretization
L = 1. #Total x length
dx = L/size

timestep = 1000
Time = 1000.
dt = Time/timestep

kappa = 0.00004

K = np.tri(size,k=1)-np.tri(size,k=-2)-3*np.identity(size)

#implicit flips a sign
K = -K/dx**2*dt*kappa + 1*np.identity(size)

#Sets boundary conditions y(0)=0 y(L)=0
K[0,0]=1
K[0,1]=0
K[1,0]=0

K[size-1,size-1]=1
K[size-1,size-2]=0
K[size-2,size-1]=0

print K

x=np.linspace(0,L,size)
y = np.zeros((timestep,size))
"""
#Initial Condition. Y(x,0)=random
y[0,:]=np.random.rand(size)
"""
#Delta function initial conditions
y[0,size/2]= 10

G = np.linalg.inv(K)
#The solver
for i in range(1,timestep):
    y[i,:]=np.dot(K,y[i-1,:])
    
#Generates a Series of images for a Movie
"""
for i in range(timestep):
    plt.clf()
    plt.plot(x,y[i,:])
    #plt.axis([0,size,0,1])
    name = "Heat/"+str('%03d' % i)+".png"
    plt.savefig(name)
"""

leg = []
#plt.plot(x,y[0,:])
#leg.append('t = 0')
for i in range(1,5):
    plt.plot(x,y[timestep/(6-i),:])
    leg.append('t = ' + str(i))
plt.legend(leg)
plt.title("Delta Function Heat Equation")
plt.show()
    


