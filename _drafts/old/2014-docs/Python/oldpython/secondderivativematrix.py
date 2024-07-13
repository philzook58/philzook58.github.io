import numpy as np
import scipy as sp
import matplotlib.pyplot as plt


size = 10

K = np.tri(size,k=1)-np.tri(size,k=-2)-3*np.identity(size) #2nd deriv matrix, no dx
x = np.linspace(0,sp.pi,size)

T = np.tri(size,k=1)-np.tri(size,k=-1)-2*np.identity(size)
print T


K2prime = K
K2prime[0,0]=1
K2prime[0,1]=0
K2prime[size-1,size-1]=1
K2prime[size-1,size-2]=0
print K2prime
dx = x[0]-x[1]

D2 = -K/(dx**2) #actuall divided by dx matrix

y = np.sin(x)
d2y = np.dot(D2,y) #This is matrix multiplication?

print K
print np.linalg.eig(K)[0]
print np.linalg.eig(K2prime)[0]#array of eignevalues #HmmK2Prime has identical eigenvalues
#must be essentially the same matrix.
print np.linalg.inv(K)*9

#np.invert(D2)
plt.plot(x,y)
plt.plot(x[1:99],d2y[1:99])
#plt.show()

#The endpoints of the matrix freakin explode out of the ass
