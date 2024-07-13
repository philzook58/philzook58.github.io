import numpy as np
import scipy as sp
import matplotlib.pyplot as plt


seedvalue = 0.1 #Initial value to start iterating on

binnum = 100
points = 100

# Iteration function
def func(y):
#    return y**2-2
    return (2*y)%1 #Goes way wrong



x = np.zeros(points)
x[0]=seedvalue

for i in range(1,points):
    x[i]=func(x[i-1])

plt.hist(x,binnum,range=(0,1))
plt.show()
