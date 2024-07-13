import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
dx = .1
x = np.arange(0,10+dx,dx)

y = np.cos(3.14/10*x)
y[0]=0
y[len(y)-1]=0
plt.plot(x,y)

def graddescent(x,y,f,delta):
    df = grad(y,f,delta)
    z = np.zeros(len(y))
    z[:] = y[:] - df[:]
    #z[0]=0
    #z[len(y)-1]=0
    return z
#/np.sqrt(dx*np.dot(z,z))

def grad(y,f,delta):
    originalaction = f(y)
    g = np.zeros(len(y))
    z = np.zeros(len(y))
    for i in range(1,len(y)-1):
        z[:] = y[:]
        z[i]=y[i]+delta
        g[i]=(f(z)-originalaction)/delta
    return g

def deriv2(y):
    z = np.zeros(len(y))
    for i in range(1,len(y)-1):
        z[i] = y[i+1]-y[i-1]

    z[0]=z[1]
    z[len(y)-1] = z[len(y)-2]
    z = z/2/dx
    return z

def action(y):
    dy = deriv2(y)
    return np.dot(dy,dy)/np.dot(y,y)


def rayleigh(x,y,minim):
    return graddescent(x,y,minim,.1)

sol = rayleigh(x,y,action)
plt.plot(x,sol)
for i in range(0,10):
    sol = rayleigh(x,sol,action)
    plt.plot(x,sol)
plt.show()
