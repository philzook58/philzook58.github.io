import scipy as sp
import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import fmin_bfgs
from scipy import interpolate





def action(minimizevars,args=0):

    #unpack minimizers
    y = np.hstack((np.zeros(1),minimizevars[0:size],np.zeros(1)))
   # multipliers = minimizevars[size-1:]
    
    yspline = interpolate.splrep(x,y,s=0) #creates spline of y
    dy = interpolate.splev(xfine,yspline,der=1) #evaluates derivative
    lagrangian = dy**2 #lagrangian of the action (passed argument?)

    lagrangianspline = interpolate.splrep(xfine,lagrangian,s=0) #spline of lagragian
    yfine = interpolate.splev(xfine,yspline)
    normfunc = yfine**2 #calculate norm of function. Possible weighting here.
    normspline = interpolate.splrep(xfine,normfunc,s=0) #creates spline of norm
    norm = interpolate.splint(x[0],x[len(x)-1],normspline)
    
    actionvalue = interpolate.splint(x[0],x[len(x)-1],lagrangianspline) #returns integrated lagrangian
    """
    constraintspline = interpolate.splrep(x,np.sin(x),s=0)
    constraint = interpolate.splev(xfine,constraintspline)
    dot=yfine*constraint
    dotprodspline = interpolate.splrep(xfine,dot,s=0) #creates spline of norm
    dotprod = interpolate.splint(x[0],x[len(x)-1],dotprodspline)
    """
    #contraints = lambd[0] * y[0] + lambd[1]*y[len(y)-1]
    
    return (actionvalue)/norm# + multipliers[0]*dotprod



def plotcurve(y):
    y = np.hstack((np.zeros(1),y,np.zeros(1)))
    yspline = interpolate.splrep(x,y,s=0)

    yfine = interpolate.splev(xfine,yspline)
    plt.plot(xfine,yfine)
    plt.plot(xfine,yfine/np.sin(xfine))

size = 5
a = 0
b = sp.pi
x = np.linspace(a,b,size+2)
y = np.ones(size);
xfine = np.linspace(a,b,100)
#yact = action(y)
y1 = fmin_bfgs(action,y)
y = np.ones(size+1)
#y2 = fmin_bfgs(action,y,args=(y1))


"""
for i in range(1000):
    y,yact=optimize(y,yact)
    #plotcurve(y)

"""

plotcurve(y1)
#plt.plot(xfine,y1/np.sin(xfine))

plt.show()

