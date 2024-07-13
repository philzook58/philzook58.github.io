import numpy as np
from scipy import linalg
import matplotlib.pyplot as plt

#endpoints and number of points
minx =-20.
maxx= 20.
size = 5


# Construct Centered Difference Matrix Q
firstcol = np.zeros(size)
firstcol[-1] = 0
firstcol[0] = -1
firstcol[1] = 1
F = linalg.circulant(firstcol)
F[0,]=0
#F[-1,0]=0

dx= ((maxx-minx)/size)
F=F/dx


x = np.linspace(minx,maxx,size)


#Construct entire equation matrix
L = -F - np.diag(x)
L[0,:]=0
#L[-1,:]=0
print L
"""
(eigval,eigvec)=linalg.eig(L)
#print eigvec[size/2-2:size/2+2,:]
#print eigvec[1,:]
print eigval[size/2]

plt.plot(x,np.abs(eigvec[size/2,:]))

plt.plot(x,np.abs(eigvec[size/2+2,:]))
plt.plot(x,np.abs(eigvec[size/2-2,:]))
"""

(Q,R)=linalg.qr(L)

print R
plt.plot(x,Q[:,-1])


plt.show()


