import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
from scipy.optimize import fmin_bfgs
from scipy import interpolate


def action(minimizevars):
    
    
    #unpack minimizers
    y = np.hstack((np.zeros(1),minimizevars[1:],np.zeros(1)))
    lambd = minimizevars[0]

    
    yspline = interpolate.splrep(x,y,s=0) #creates spline of y
    dy = interpolate.splev(x,yspline,der=1) #evaluates derivative
    lagrangian = dy**2 + lambd*(np.sin(x)*y) #lagrangian of the action (passed argument?)

    lagrangianspline = interpolate.splrep(x,lagrangian,s=0) #spline of lagragian

    normfunc = y**2 #calculate norm of function. Possible weighting here.
    normspline = interpolate.splrep(x,normfunc,s=0) #creates spline of norm
    norm = interpolate.splint(x[0],x[len(x)-1],normspline)
    
    actionvalue = interpolate.splint(x[0],x[len(x)-1],lagrangianspline) #returns integrated lagrangian

    #contraints = lambd[0] * y[0] + lambd[1]*y[len(y)-1]
    
    return actionvalue/norm


grid = 10
a = 0 #beginning of interval
b = sp.pi #end of interval
x = np.linspace(a,b,grid) 
y = x*(sp.pi-x)*(1-x)

plt.plot(x,y)
minimizevars = np.hstack((np.zeros(1),y[1:len(y)-1])) #don't optimize endpoints. They aren't variable
sol = fmin_bfgs(action,minimizevars)
soly= np.hstack((np.zeros(1),sol[1:],np.zeros(1))) #puts endpoints back
plt.plot(x,soly)
plt.show()
