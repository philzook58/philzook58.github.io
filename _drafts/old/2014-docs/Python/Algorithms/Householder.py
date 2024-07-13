# -*- coding: utf-8 -*-
"""
Created on Mon Jan 21 12:52:31 2013

@author: Philip
"""

import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
from scipy import linalg
from numpy import linalg as LA


size = 3

A = np.random.random((size,size))
U=np.zeros((size,size))
R = np.zeros((size,size))
def reflect(x,u):
    return x - 2 * np.dot(np.outer(u,u),x)
R[:,:]=A[:,:]

for i in range(size):
    
    w =  np.copy(R[i:,i])
    w[0] = w[0]- LA.norm(w)
    print LA.norm(w)
    u = w/LA.norm(w)

    U[i:,i]=u
    R = reflect(R,U[:,i])

Q = np.identity(size)

for i in range(size):
    Q = reflect(Q,U[:,size-i-1])

print A
print R
print Q
print LA.qr(A)
print np.dot(Q,R)