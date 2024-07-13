import scipy as sp
import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import fmin_bfgs
from scipy import interpolate



def action(minimizevars):

    #unpack minimizers
    y = np.hstack((np.zeros(1),minimizevars,np.zeros(1)))
    
    yspline = interpolate.splrep(x,y,s=0) #creates spline of y
    dy = interpolate.splev(xfine,yspline,der=1) #evaluates derivative
    lagrangian = dy**2 #lagrangian of the action (passed argument?)

    lagrangianspline = interpolate.splrep(xfine,lagrangian,s=0) #spline of lagragian
    yfine = interpolate.splev(xfine,yspline)
    normfunc = yfine**2 #calculate norm of function. Possible weighting here.
    normspline = interpolate.splrep(xfine,normfunc,s=0) #creates spline of norm
    norm = interpolate.splint(x[0],x[len(x)-1],normspline)
    
    actionvalue = interpolate.splint(x[0],x[len(x)-1],lagrangianspline) #returns integrated lagrangian

    #contraints = lambd[0] * y[0] + lambd[1]*y[len(y)-1]
    
    return (actionvalue)/norm




def optimize(f,fact):
    ftest = np.copy(f)
    randindex = np.random.randint(0,size-1)
    ftest[randindex] += (-1)**np.random.randint(1,2)*np.random.rand()
    ftact = action(ftest)
    
    if fact < ftact:
        #print("Lo")
        return [f,fact]
    else:
        #print("Hi")
        print(str(ftact)+ " > " + str(fact))
        return [ftest,ftact]

def plotcurve(y):
    y = np.hstack((np.zeros(1),y,np.zeros(1)))
    yspline = interpolate.splrep(x,y,s=0)

    yfine = interpolate.splev(xfine,yspline)
    plt.plot(xfine,yfine)

size = 2
a = 0
b = sp.pi
x = np.linspace(a,b,size+2)
y = np.ones(size);
xfine = np.linspace(a,b,100)
yact = action(y)
for i in range(1000):
    y,yact=optimize(y,yact)
    #plotcurve(y)



plotcurve(y)
plt.show()

