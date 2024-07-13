import numpy as np
import scipy as sp
import matplotlib.pyplot as plt

#Creating Green's Function From Matrices - Philip Zucker 2011

size = 51 #total domain size
steps = 1
K = np.tri(size,k=1)-np.tri(size,k=-2)-3*np.identity(size) #second deriv matrix


#boundary condition manipulations. Makes symmettric
K[0,0]=1
K[0,1]=0
K[1,0]=0

K[size-1,size-1]=1
K[size-1,size-2]=0
K[size-2,size-1]=0

print K
x=range(size)

""" #plot eigenvectors of K
#print np.linalg.eig(K)
for i in range(size):
    plt.plot(x,np.linalg.eig(K)[1][i])
    plt.show()
"""

#Plots all the green's functions
G = np.linalg.inv(K)
print G
x=range(size)
for i in range(size):
    plt.plot(x,G[i])

plt.show()

    


