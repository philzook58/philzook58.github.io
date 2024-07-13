import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
from scipy import linalg


size = 3

A = np.random.random((size,size))


U = np.zeros((size,size))
L= np.zeros((size,size))

U[:,:]=A[:,:]


for row in range(size):
    L[row,row]=U[row,row]
    U[row,:]=U[row,:]/U[row,row]

    for lowerrow in range(row+1,size):
        L[lowerrow,row]=U[lowerrow,row]
        U[lowerrow,:] = U[lowerrow,:] - U[lowerrow,row]*U[row,:]

print "A = "        
print A

print "My U ="
print U
print "My L ="

print L
"""
print "P ="
print linalg.lu(A)[0]
print "L ="
print linalg.lu(A)[1]
print "U ="
print linalg.lu(A)[2]
"""
print np.dot(L,U)

