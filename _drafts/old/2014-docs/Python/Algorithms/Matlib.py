# -*- coding: utf-8 -*-
"""
Created on Sun Jan 20 01:19:49 2013
Matrix Construction Module
@author: Philip
"""

import numpy as np
from scipy import linalg

#FixedFixed
def K(size):
    firstcol = np.zeros(size)
    firstcol[0] = 2
    firstcol[1] = -1
    
    firstrow = np.zeros(size)
    firstrow[0] = 2
    firstrow[1] = -1
    return linalg.toeplitz(firstcol,firstrow)
    
def C(size):
    
    firstrow = np.zeros(size)
    firstrow[-1] = -1
    firstrow[0] = 2
    firstrow[1] = -1
    
    return linalg.circulant(firstrow)
    
#Fixed-Free
def T(size):
    temp = K(size)
    temp[0,0]=1
    return temp

#Free Free ends 
def F(size):
    temp = T(size)
    temp[-1,-1]=1
    return temp

    
    
