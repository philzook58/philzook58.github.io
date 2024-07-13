import scipy as sp
import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import fmin_bfgs
from scipy import interpolate



class minimizeWrapper:
    size = 0
    y = np.zeros(size)
    multipliers = np.zeros(0)
    def __init__(self,minimizevars,siz):
        self.size = siz
        self.y = self.function(minimizevars)
        multipliers = self.mults(minimizevars)   
    def function(self,var):
        return np.hstack((np.zeros(1),var[0:self.size],np.zeros(1)))
    def mults(self,var):
        return var[self.size-1:]
    def fine(self,xfine,x,y):
        if len(xfine) == len(x):
            return y
        yspline = interpolate.splrep(x,y,s=0) #creates spline of y
        return interpolate.splev(xfine,yspline)
    def deriv(self,xfine,y):
        yspline = interpolate.splrep(x,y,s=0) #creates spline of y
        return interpolate.splev(xfine,yspline,der=1)
    def integrate(self,x,y):
        yspline = interpolate.splrep(x,y,s=0)
        return interpolate.splint(x[0],x[len(x)-1],yspline)
    def norm(self,xfine,x,y):
        yfine = self.fine(xfine,x,y)
        yfine=yfine**2
        return self.integrate(xfine,yfine)
    def normdotprod(self,xfine,x,f1):
        f1fine = self.fine(xfine,x,f1)
        normfactor = np.sqrt(self.norm(xfine,xfine,f1fine)*self.norm(xfine,xfine,np.sin(xfine)))
        return self.integrate(xfine,f1fine*np.sin(xfine))/normfactor
        
    

def action(minimizevars,args=0):


    mini = minimizeWrapper(minimizevars,size) # Create wrapper of function
    y = mini.y #The function part
    
    dy = mini.deriv(xfine,y)

    lagrangian = dy**2 #lagrangian of the action
    actionvalue = mini.integrate(xfine,lagrangian)
    norm = mini.norm(xfine,x,y)
    
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

size = 7
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

