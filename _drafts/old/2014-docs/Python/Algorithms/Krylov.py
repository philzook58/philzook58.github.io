import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
from scipy import linalg

#constructs orthonormal krylov subspace

krydim = 3
dim = 6
points = np.arange(1,dim+1)
A = np.vander(points)
print A

b = np.ones(dim)

Krylov = np.zeros((krydim,dim))
Krylov[0,:]=b/linalg.norm(b)

for i in range(1,krydim):
    temp = np.dot(A,Krylov[i-1,:])
    print temp
    for j in range(i):
        temp = temp - Krylov[j,:] * np.dot(temp,Krylov[j,:])
    Krylov[i,:]=temp/linalg.norm(temp)

print Krylov

print np.dot(Krylov[0,:],Krylov[2,:])
