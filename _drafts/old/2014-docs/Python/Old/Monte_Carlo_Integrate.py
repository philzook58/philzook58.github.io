import numpy as np
import scipy as sp
from matplotlib import pyplot as plt
from scipy import integrate as integ

steps =100

a = 1
b = 3

def f(x):
    return x #np.sin(3.14*x)**2

def new():
    return np.random.random()*(b-a)+a


#Wants to sample points in a distribution proportional to f
#Uses Metropolis algorithm to generate right distribution
def MonteCarloStep(xold,g):
    xnew = new()
    # minimum of 1 , xnew/xold
    acceptprob = g(xnew) / g(xold)
    if acceptprob > 1:
        return xnew
    #accept with prob fxnew/fxold
    else:
        if np.random.random() < acceptprob: #acceptance probablity
            return xnew
        else:
            return xold

def integrate(g):
    x = np.random.random()*(b-a) + a
    integral = 0
    xarray = []
    for i in range(steps):
        x = MonteCarloStep(x,g)
        xarray.append(x)
        integral += x/steps
        print integral*steps/(i+1)
    plt.hist(xarray,20)
    #plt.show()
    return integral

solution =  integrate(f)
actual = integ.quad(f,a,b)[0]
print solution
print actual
print "error = " + str(100*(solution-actual)/actual) + "%"
