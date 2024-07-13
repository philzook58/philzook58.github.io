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
mublue = [-1,-1]

sigmared = 1
sigmablue= 3

reds = np.random.randn(points,2)
blues = np.random.randn(points,2)

reds[:,0] = sigmared * reds[:,0] + mured[0]
reds[:,1] = sigmared * reds[:,1] + mured[1]
blues[:,0] = sigmablue * blues[:,0] + mublue[0]
blues[:,1] = sigmablue * blues[:,1] + mublue[1]

plt.scatter(reds[:,0],reds[:,1], c = 'r')
plt.scatter(blues[:,0],blues[:,1], c='b')
plt.show()