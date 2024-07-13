# -*- coding: utf-8 -*-
"""
Created on Sun Mar 31 15:43:16 2013

@author: Philip
"""

import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
from scipy import linalg

points = 100

mured = [1,-1]
mublue = [-1,-1]

sigmared = 1.
sigmablue= 1.


reds = np.random.randn(points,2)
blues = np.random.randn(points,2)

reds[:,0] = sigmared * reds[:,0] + mured[0]
reds[:,1] = sigmared * reds[:,1] + mured[1]
blues[:,0] = sigmablue * blues[:,0] + mublue[0]
blues[:,1] = sigmablue * blues[:,1] + mublue[1]


w = np.zeros(2)
data = np.zeros(3)
b=0
#blues postivie, reds negative
for i in range(1000):
    #print w
    #print b
    point = np.random.randint(points)
    if np.random.randint(2)==0:
        #data[0:2] = reds[point,:]
        #data[2]=1
        if np.dot( w , reds[point,:] ) +b >= 0:
            w[:] = w[:] - reds[point,:]
            b = b - 1
    else:
        #data[0:2] = blues[point,:]
        #data[2]=-1
        if np.dot( w , blues[point,:] ) + b <= 0:
                   
            w[:] = w[:] + blues[point,:]
            b = b + 1
    #if 
            
x= np.linspace(-2,2,100)
y = (-x*w[0]-b)/w[1]
print w
print b

plt.scatter(reds[:,0],reds[:,1], c = 'r')
plt.scatter(blues[:,0],blues[:,1], c='b')
plt.plot(x,y)
plt.show()