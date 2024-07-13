import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
from scipy.optimize import fmin_bfgs
from scipy import interpolate


def action(minimizevars):
    
    
    #unpack minimizers
    y = np.hstack((0,minimizevars,1))
    
    yspline = interpolate.splrep(x,y,s=0) #creates spline of y
    dy = interpolate.splev(x,yspline,der=1) #evaluates derivative
    lagrangian = (1-x**2)*dy**2 #lagrangian of the action (passed argument?)

    lagrangianspline = interpolate.splrep(x,lagrangian,s=0) #spline of lagragian

    normfunc = y**2 #calculate norm of function. Possible weighting here.
    normspline = interpolate.splrep(x,normfunc,s=0) #creates spline of norm
    norm = interpolate.splint(x[0],x[len(x)-1],normspline)
    
    actionvalue = interpolate.splint(x[0],x[len(x)-1],lagrangianspline) #returns integrated lagrangian

    #contraints = lambd[0] * y[0] + lambd[1]*y[len(y)-1]
    
    return (actionvalue)/norm


grid = 20
a = 0 #beginning of interval
b = 1 #sp.pi #end of interval
x = np.linspace(a,b,grid) 
y = x #np.random.rand(grid)

plt.plot(x,y)
minimizevars = y[1:len(y)-1] #don't optimize endpoints. They aren't variable
sol = fmin_bfgs(action,minimizevars)
soly= np.hstack((np.zeros(1),sol,np.zeros(1))) #puts endpoints back
plt.plot(x,soly)
plt.show()
