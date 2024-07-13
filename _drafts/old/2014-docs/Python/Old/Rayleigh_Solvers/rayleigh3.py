import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
from scipy.optimize import fmin
from scipy import interpolate


def deriv2(y):
    z = np.zeros(len(y))
    for i in range(1,len(y)-1):
        z[i] = y[i+1]-y[i-1]

    z[0]=z[1]
    z[len(y)-1] = z[len(y)-2]
    z = z/2/dx
    return z

def action(y):
    tck = interpolate.splrep(x,y,s=0)
    dy = interpolate.splev(x,tck,der=1)
    return np.dot(dy,dy)/np.dot(y,y) + 100000*(y[0]**2+y[len(y)-1]**2)

dx = 0.1
x = np.arange(0,10,dx)
y = np.ones(len(x))
plt.plot(x,fmin(action,y,xtol=0.01))
plt.show()

