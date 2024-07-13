import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
from scipy.optimize import fmin
from scipy import interpolate


def action(x,y):
    yspline = interpolate.splrep(x,y,s=0) #creates spline of y
    dy = interpolate.splev(x,yspline,der=1) #evaluates derivativw
    lagrangian = dy**2 #lagrangian of the action (passed argument?)
    lagrangianspline = interpolate.splrep(x,lagrangian,s=0) #spline of lagragian
    return interpolate.splint(x[0],x[len(x)-1],lagrangianspline) #returns integrated lagrangian

grid = 10
a = 0 #beginning of interval
b = sp.pi #end of interval
x = np.linspace(a,b,grid) 
y = np.sin(x)
plt.plot(x,y)

ans = action(x,y) 
print ans 
print sp.pi/2 #correct answer to integral of cos^2
print "Error:" + str((sp.pi/2 - ans)*2/sp.pi * 100) + "%"
print "Not bad!"


