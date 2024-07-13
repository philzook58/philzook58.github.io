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

mured = [1,1]
mublue = [0,-1]

sigmared = 1.
sigmablue= 1.


reds = np.random.randn(points,2)
blues = np.random.randn(points,2)

reds[:,0] = sigmared * reds[:,0] + mured[0]
reds[:,1] = sigmared * reds[:,1] + mured[1]
blues[:,0] = sigmablue * blues[:,0] + mublue[0]
blues[:,1] = sigmablue * blues[:,1] + mublue[1]

def error(we,be):
    err = 0
    for point in range(points):
        if np.dot( we , reds[point,:] ) +be >= 0:
            err = err + 1
        if np.dot( we , blues[point,:] ) + be <= 0:
            err = err + 1
    return err
        
    
bestw = np.zeros(2)
bestb = 0
besterror = points*2

w = np.zeros(2)

b=0
#blues postivie, reds negative
for i in range(1000):
    #print w
    #print b
    point = np.random.randint(points)
    if np.random.randint(2)==0:      
        if np.dot( w , reds[point,:] ) + b >= 0:
            w[:] = w[:] - reds[point,:]
            b = b - 1
    else:       
        if np.dot( w , blues[point,:] ) + b <= 0:
                   
            w[:] = w[:] + blues[point,:]
            b = b + 1
            
    err = error(w,b)
    if err < besterror:
        bestw[:] = w[:]
        bestb = b
        besterror = err
        print "update"
        
    

w[:] = bestw[:]
b = bestb
err = besterror
x= np.linspace(-2,2,100)
y = (-x*w[0]-b)/w[1]
print w
print b
print err

plt.scatter(reds[:,0],reds[:,1], c = 'r')
plt.scatter(blues[:,0],blues[:,1], c='b')
plt.plot(x,y)
plt.show()