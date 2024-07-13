import numpy as np
import scipy as sp
import matplotlib.pyplot as plt


c = 1 #this constant is C^2*dt^2/dx^2
size = 10
steps = 1
K = np.tri(size,k=1)-np.tri(size,k=-2)-3*np.identity(size)
#K = c*K + np.identity(size)
K[0,0]=1
K[0,1]=0
K[size-1,size-1]=1
K[size-1,size-2]=0

print K

G = np.linalg.inv(K)
print G

u = np.zeros((steps+2,size))

x = np.linspace(0,sp.pi,size)
u[0,:] = np.sin(x) #Setting initial conditions
u[1,:] = np.sin(x)
print u

#for i in range(steps):
    


