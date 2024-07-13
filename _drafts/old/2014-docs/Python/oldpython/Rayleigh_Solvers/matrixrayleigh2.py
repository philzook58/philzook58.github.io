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

def unitvector(y):
    v = np.hstack((y,np.sqrt(abs(1-np.dot(y,y)))))
    return v
"""
def gradaction(y):
    return np.dot((K + np.identity(size)*action(y))/np.dot(y,y),2*y)

def action(y):
    return -np.dot(y,np.dot(K,y))/np.dot(y,y)

def action2(y):
    return (-np.dot(y,np.dot(K,y)) + 100*np.dot(y,u)**2/np.dot(u,u))/np.dot(y,y)
"""

def action(v):
    y = unitvector(v)
    return -np.dot(y,np.dot(K,y))

def action2(v):
    y = unitvector(v)
    return (-np.dot(y,np.dot(K,y)) + 1000*np.dot(y,sol)**2)
guess = np.ones(size-1)
u = fmin(action,guess)
sol = unitvector(u)
x=range(size)
z = fmin(action2,guess)
plt.plot(x,sol)
f = unitvector(z)
plt.plot(x,f)


plt.show()

    


