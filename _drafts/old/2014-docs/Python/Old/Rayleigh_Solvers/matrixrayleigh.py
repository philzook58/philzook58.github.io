import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
from scipy.optimize import fmin


c = 1 #this constant is C^2*dt^2/dx^2
size = 10


K = np.tri(size,k=1)-np.tri(size,k=-2)-3*np.identity(size)
"""
K[0,0]=1
K[0,1]=0
K[1,0]=0

K[size-1,size-1]=1
K[size-1,size-2]=0
K[size-2,size-1]=0
"""

print K

y = np.ones(size)
print np.dot(K,y)
print np.dot(y,y)

def action(y):
    return -np.dot(y,np.dot(K,y))/np.dot(y,y)

def action2(y):
    return (-np.dot(y,np.dot(K,y)) + 100*np.dot(y,u)**2/np.dot(u,u))/np.dot(y,y)


u = fmin(action,y)
x=range(size)
z = fmin(action2,y)
plt.plot(x,u)
plt.plot(x,z/np.sqrt(np.dot(z,z)))


plt.show()

    


