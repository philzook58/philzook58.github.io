# -*- coding: utf-8 -*-
"""
Created on Sat Jan 19 10:22:06 2013
A scaling LU factorization. Sort of taking a cantor set ordering?
@author: Philip
"""
import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
from scipy import linalg
import Matlib

np.set_printoptions(precision = 1,)

#The Size of the grid and the division scheme
gridbase = 2
gridpow = 5
gridnum=gridbase**gridpow + 1

#Construct matrix (second derivative) and reaarange to ordering

K = Matlib.T(gridnum)

# create rodering array
reord = np.zeros(gridnum)
reord[0]=0
reord[1]=gridnum - 1
n= 2
for i in range(gridpow):
    for j in range(gridnum):
        if(j % gridbase**(gridpow-i) != 0 and j % gridbase**(gridpow-i-1) == 0):
            reord[n]=j
            n=n+1
print reord            

F = np.zeros((gridnum,gridnum))

#create resorted matirx F
for i in range(gridnum):
    for j in range(gridnum):
        F[-i,-j] = K[reord[i],reord[j]] 

print F

#LU decomposition
U = np.zeros((gridnum,gridnum))
L = np.zeros((gridnum,gridnum))

U[:,:]=F[:,:]

for row in range(gridnum):
    L[row,row]=U[row,row]
    U[row,:]=U[row,:]/U[row,row]

    for lowerrow in range(row+1,gridnum):
        L[lowerrow,row]=U[lowerrow,row]
        U[lowerrow,:] = U[lowerrow,:] - U[lowerrow,row]*U[row,:]
        
print U
print L
print np.dot(L,U)
print linalg.inv(L)
plt.matshow(F)
plt.matshow(L)
plt.matshow(U)
plt.matshow(linalg.inv(L))
plt.show()