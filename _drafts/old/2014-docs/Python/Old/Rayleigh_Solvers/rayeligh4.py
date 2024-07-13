import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
from scipy.optimize import fmin_bfgs
from scipy import interpolate


def action(y):
    #Enforce Boundary Conditions
    y[0]=0
    y[len(y)-1]=0
    
    yspline = interpolate.splrep(x,y,s=0) #creates spline of y
    dy = interpolate.splev(x,yspline,der=1) #evaluates derivative
    lagrangian = dy**2 #lagrangian of the action (passed argument?)
    lagrangianspline = interpolate.splrep(x,lagrangian,s=0) #spline of lagragian

    normfunc = y**2 #calculate norm of function. Possible weighting here.
    normspline = interpolate.splrep(x,normfunc,s=0) #creates spline of norm
    norm = interpolate.splint(x[0],x[len(x)-1],normspline)
    
    actionvalue = interpolate.splint(x[0],x[len(x)-1],lagrangianspline) #returns integrated lagrangian

    return actionvalue/norm


grid = 10
a = 0 #beginning of interval
b = sp.pi #end of interval
x = np.linspace(a,b,grid) 
y = np.sin(x)

plt.plot(x,y)
sol = fmin_bfgs(action,y)
plt.plot(x,sol)
plt.show()
