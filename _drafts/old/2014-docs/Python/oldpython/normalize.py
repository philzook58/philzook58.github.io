import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
dx = .1
x = np.arange(0,10+dx,dx)
print x
print len(x)
print range(1,len(x)-1)
print np.zeros(len(x))
y = np.sin(3.14/10*x)
#y[0]=0
#y[len(y)-1]=0
#plt.plot(x,y)
y = y/np.sqrt(dx*np.dot(y,y))
plt.plot(x,y)


def deriv2(y):
    z = np.zeros(len(y))
    for i in range(1,len(y)-1):
        z[i] = y[i+1]-y[i-1]

    z[0]=z[1]
    z[len(y)-1] = z[len(y)-2]
    z = z/2/dx
    
    return z

def sumsin(y):
    return np.sum(np.sin(y))

def grad(y,f,delta):
    originalaction = f(y)
    g = np.zeros(len(y))
    z = np.zeros(len(y))
    for i in range(1,len(y)-1):
        z[:] = y[:]
        print z
        z[i]=y[i]+delta
        
        g[i]=(f(z)-originalaction)/delta
    print g
    return g

f = grad(x,sumsin,1.)
plt.plot(x,f)

#plt.plot(x,deriv2(y))
plt.show()
