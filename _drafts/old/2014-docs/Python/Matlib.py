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

def Dc(size): #periodic first derivative
    
    firstrow = np.zeros(size)
    firstrow[-1] = -1
    firstrow[0] = 1

    
    return linalg.circulant(firstrow)

#Bloch Boundary conditions; z = e^(ika) 
def B(size,z):
    temp = C(size)
    temp[0,-1]=z
    #temp[-1,0]=
    
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
#Retarded
def R(size):
    firstcol = np.zeros(size)
    firstcol[0] = -1
    firstcol[1] = 2
    firstcol[2] = -1
    
    
    firstrow = np.zeros(size)
    firstrow[0] = -1

    temp = linalg.toeplitz(firstcol,firstrow)
    temp[0,0]=1
    temp[1,0]=-1
    temp[1,1]=1
    return temp


#Advanced
#def A(size):
    
    
    
