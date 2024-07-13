import scipy as sp
import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import fmin_bfgs
from scipy import interpolate



class minimizeWrapper:
    size = 0
    y = np.zeros(size)
    def __init__(self,minimizevars=[],siz=0):
        self.size = siz
        self.y = self.function(minimizevars)
    
    def function(self,var):
        return np.hstack((np.zeros(1),var[0:self.size],np.zeros(1)))
    def fine(self,xfine,x,y): #Interpolates x,y into xfine,yfine
        if len(xfine) == len(x):
            return y
        yspline = interpolate.splrep(x,y,s=0) #creates spline of y
        return interpolate.splev(xfine,yspline)
    def deriv(self,xfine,y): #Interpolates derivative
        yspline = interpolate.splrep(x,y,s=0) #creates spline of y
        return interpolate.splev(xfine,yspline,der=1)
    def integrate(self,x,y): #Interpolates and integrates
        yspline = interpolate.splrep(x,y,s=0)
        return interpolate.splint(x[0],x[len(x)-1],yspline)
    def norm(self, xfine, x, y): #Gives back the norm
        yfine = self.fine(xfine,x,y)
        yfine=yfine**2 * weight(xfine)
        return self.integrate(xfine,yfine)

def weight(x):
    return x

def action(minimizevars,args=0):

    mini = minimizeWrapper(minimizevars,size) # Create wrapper of function
    y = mini.y #The coarse function values
    dy = mini.deriv(xfine,y)
    yfine = mini.fine(xfine,x,y)
    lagrangian = xfine*dy**2 + 1/(xfine+0.00001)*yfine**2 #lagrangian of the action
    actionvalue = mini.integrate(xfine,lagrangian)
    norm = mini.norm(xfine,x,y) 
    return (actionvalue)/norm

def plotcurve(x,xfine,y,i):
    mini = minimizeWrapper(y,size) # Create wrapper of function
    yfine = mini.fine(xfine,x,mini.y)#Interpolate y
    yfine = yfine / np.sqrt(mini.norm(xfine,xfine,yfine))
    plt.figure(1)
    plt.plot(xfine,yfine)
    plt.figure(2)
    plt.plot(xfine,yfine-actual) #Compare to correct answer

size = 7
a = 0
b = 3.8317060
x = np.linspace(a,b,size+2)
y = np.ones(size);
xfine = np.linspace(a,b,100)
leg = []
mini = minimizeWrapper()
plt.figure(1)
bessel = sp.special.jn(1,xfine)
actual = bessel/np.sqrt(mini.norm(xfine,xfine,bessel))
for i in range(2,7):
    size = i
    x = np.linspace(a,b,size+2)
    y = np.ones(size);
    y = fmin_bfgs(action,y)
    plotcurve(x,xfine,y,i)
    leg.append(str(i) + ' Parameters')



plt.figure(2)
plt.legend(leg)
plt.title("Difference Error")
plt.figure(1)
leg.append('Actual')
plt.plot(xfine,actual)
plt.legend(leg)
plt.title("$\lambda_0$ Eigenfunction")

    
plt.show()

