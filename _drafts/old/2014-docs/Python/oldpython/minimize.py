import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
from scipy.optimize import fmin

def simplewell(x):
    return sum((x-3)*(x-3))

sol = np.random.rand(5)
x = np.random.rand(5)
print x
print fmin(simplewell,x,xtol=0.01)


