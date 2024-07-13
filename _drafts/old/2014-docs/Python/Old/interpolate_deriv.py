import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
from scipy.optimize import fmin
from scipy import interpolate



dx = 1
x = np.linspace(0,10,10)

y = np.sin(x)
plt.plot(x,y)

xnew= np.linspace(0,10,100)
tck = interpolate.splrep(x,y,s=0) #creates a spline for the data passed
dy = interpolate.splev(xnew,tck,der=1) #evaluates derivative of spline
y2 = interpolate.splev(xnew,tck)
ytrue = np.sin(xnew)
plt.plot(xnew,dy)
plt.plot(xnew,y2)
plt.plot(xnew,ytrue)
plt.show()
