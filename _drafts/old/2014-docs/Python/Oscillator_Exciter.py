import numpy as np
import scipy as sp
from scipy import integrate
import matplotlib.pyplot as plt


F = 3 # Force amplitude
k = 1  #Spring Constant
hifreq = .1
lowfreq= 2
a = .1 # x^3 forcing term coeffcient
b = .1 # damping ciefficient
sweepfreq = .0001 #Should be much lower than the others


tarray = np.linspace(0,1/sweepfreq,2000)


def freq(t):
    return lowfreq + (hifreq-lowfreq) * t * sweepfreq/2

def func(y,t):
    x = y[0]
    v = y[1]
    dx = v
    dv = -k*x -a * x**3 - b*v + F * np.sin(freq(t)*t)
    return [dx,dv]


sol = integrate.odeint(func,[0,0],tarray)

#for i in range()

energy = k*sol[:,0]**2+sol[:,1]**2
#print sol[:,0]**2
amp = np.sqrt(energy)
#plt.plot(tarray,amp)
plt.plot(tarray,sol[:,0])
plt.show()
