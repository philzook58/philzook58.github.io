import numpy as np
from scipy import linalg
import matplotlib.pyplot as plt

#endpoints and number of points
minx =-20.
maxx= 20.
size = 70


# Construct Centered Difference Matrix Q
firstrow = np.zeros(size)
firstrow[-1] = 1
firstrow[0] = 0
firstrow[1] = -1
Q = linalg.circulant(firstrow)
Q[0,-1]=0
Q[-1,0]=0
dx= ((maxx-minx)/size)
Q=Q/dx


x = np.linspace(minx,maxx,size)


#Construct entire equation matrix
L = -Q - np.diag(x)

(eigval,eigvec)=linalg.eig(L)
#print eigvec[size/2-2:size/2+2,:]
#print eigvec[1,:]
print eigval[size/2]

plt.plot(x,np.abs(eigvec[size/2,:]))
plt.plot(x,np.real(eigvec[size/2,:]))
#plt.plot(x,np.imag(eigvec[size/2,:]))


#plt.plot(x,np.abs(eigvec[size/2+2,:]))
#plt.plot(x,np.abs(eigvec[size/2-2,:]))

plt.show()


