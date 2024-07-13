import numpy as np
import scipy as sp
from scipy import integrate
import matplotlib.pyplot as plt


F = .05 # Force amplitude
k =  1 #Spring Constant
hifreq = 4
lowfreq= 0
a = 0 # x^3 forcing term coeffcient
b = 0.01 # damping ciefficient
sweepfreq = .0001 #Should be much lower than the others


tarray = np.linspace(0,1/sweepfreq,2000)
freqlabel = freq(tarray)


def freq(t):
    return lowfreq + (hifreq-lowfreq) * t * sweepfreq

def func(y,t):
    x = y[0]
    v = y[1]
    dx = v
    dv = -k*(x-.1) - a * x**3 - b*v + F * np.sin(freq(t)*t) * x #+ .01* np.sin(k*t)
    return [dx,dv]


sol = integrate.odeint(func,[.1,0],tarray)

#for i in range()

energy = k*sol[:,0]**2+sol[:,1]**2
#print sol[:,0]**2
amp = np.sqrt(energy)
#plt.plot(tarray,amp)
plt.plot(freqlabel,sol[:,0])
plt.show()
